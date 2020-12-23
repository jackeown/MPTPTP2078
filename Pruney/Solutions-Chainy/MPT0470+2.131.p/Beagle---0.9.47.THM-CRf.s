%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:19 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 289 expanded)
%              Number of leaves         :   46 ( 116 expanded)
%              Depth                    :   13
%              Number of atoms          :  159 ( 399 expanded)
%              Number of equality atoms :   91 ( 235 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_68,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_70,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_29,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k4_xboole_0(A,B),C) = k4_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k4_xboole_0(A,B)) = k4_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_111,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_99,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_108,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_10,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_40,plain,(
    ! [A_46] : k1_setfam_1(k1_tarski(A_46)) = A_46 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_12,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1918,plain,(
    ! [A_271,B_272] : k1_setfam_1(k2_tarski(A_271,B_272)) = k3_xboole_0(A_271,B_272) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1927,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = k1_setfam_1(k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1918])).

tff(c_1930,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1927])).

tff(c_1968,plain,(
    ! [A_280,B_281] : k5_xboole_0(A_280,k3_xboole_0(A_280,B_281)) = k4_xboole_0(A_280,B_281) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1977,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_1930,c_1968])).

tff(c_1983,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1977])).

tff(c_819,plain,(
    ! [A_164,B_165] : k1_setfam_1(k2_tarski(A_164,B_165)) = k3_xboole_0(A_164,B_165) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_828,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = k1_setfam_1(k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_819])).

tff(c_831,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_828])).

tff(c_867,plain,(
    ! [A_169,B_170] : k5_xboole_0(A_169,k3_xboole_0(A_169,B_170)) = k4_xboole_0(A_169,B_170) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_876,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_831,c_867])).

tff(c_882,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_876])).

tff(c_36,plain,(
    ! [B_45] : k4_xboole_0(k1_tarski(B_45),k1_tarski(B_45)) != k1_tarski(B_45) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_883,plain,(
    ! [B_45] : k1_tarski(B_45) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_882,c_36])).

tff(c_62,plain,
    ( k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_113,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_64,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_48,plain,(
    ! [A_49] :
      ( r2_hidden('#skF_1'(A_49),A_49)
      | v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_115,plain,(
    ! [A_83,B_84] :
      ( r1_tarski(k1_tarski(A_83),B_84)
      | ~ r2_hidden(A_83,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_121,plain,(
    ! [A_85] :
      ( k1_tarski(A_85) = k1_xboole_0
      | ~ r2_hidden(A_85,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_115,c_8])).

tff(c_126,plain,
    ( k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_48,c_121])).

tff(c_127,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_50,plain,(
    ! [A_67,B_68] :
      ( v1_relat_1(k5_relat_1(A_67,B_68))
      | ~ v1_relat_1(B_68)
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_137,plain,(
    ! [A_88,B_89] : k1_setfam_1(k2_tarski(A_88,B_89)) = k3_xboole_0(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_146,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = k1_setfam_1(k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_137])).

tff(c_149,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_146])).

tff(c_176,plain,(
    ! [A_97,B_98] : k5_xboole_0(A_97,k3_xboole_0(A_97,B_98)) = k4_xboole_0(A_97,B_98) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_185,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_176])).

tff(c_191,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_185])).

tff(c_324,plain,(
    ! [A_116,C_117,B_118] : k4_xboole_0(k2_zfmisc_1(A_116,C_117),k2_zfmisc_1(B_118,C_117)) = k2_zfmisc_1(k4_xboole_0(A_116,B_118),C_117) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_331,plain,(
    ! [B_118,C_117] : k2_zfmisc_1(k4_xboole_0(B_118,B_118),C_117) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_191])).

tff(c_340,plain,(
    ! [C_117] : k2_zfmisc_1(k1_xboole_0,C_117) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_331])).

tff(c_6,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_58,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_727,plain,(
    ! [A_152,B_153] :
      ( k1_relat_1(k5_relat_1(A_152,B_153)) = k1_relat_1(A_152)
      | ~ r1_tarski(k2_relat_1(A_152),k1_relat_1(B_153))
      | ~ v1_relat_1(B_153)
      | ~ v1_relat_1(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_733,plain,(
    ! [B_153] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_153)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_153))
      | ~ v1_relat_1(B_153)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_727])).

tff(c_738,plain,(
    ! [B_154] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_154)) = k1_xboole_0
      | ~ v1_relat_1(B_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_6,c_60,c_733])).

tff(c_52,plain,(
    ! [A_69] :
      ( k3_xboole_0(A_69,k2_zfmisc_1(k1_relat_1(A_69),k2_relat_1(A_69))) = A_69
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_750,plain,(
    ! [B_154] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_154),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_154)))) = k5_relat_1(k1_xboole_0,B_154)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_154))
      | ~ v1_relat_1(B_154) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_738,c_52])).

tff(c_758,plain,(
    ! [B_155] :
      ( k5_relat_1(k1_xboole_0,B_155) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_155))
      | ~ v1_relat_1(B_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_340,c_750])).

tff(c_762,plain,(
    ! [B_68] :
      ( k5_relat_1(k1_xboole_0,B_68) = k1_xboole_0
      | ~ v1_relat_1(B_68)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_50,c_758])).

tff(c_766,plain,(
    ! [B_156] :
      ( k5_relat_1(k1_xboole_0,B_156) = k1_xboole_0
      | ~ v1_relat_1(B_156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_762])).

tff(c_775,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_64,c_766])).

tff(c_781,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_775])).

tff(c_782,plain,(
    k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_893,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_883,c_782])).

tff(c_894,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_901,plain,(
    ! [A_173,B_174] :
      ( r1_tarski(k1_tarski(A_173),B_174)
      | ~ r2_hidden(A_173,B_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_907,plain,(
    ! [A_175] :
      ( k1_tarski(A_175) = k1_xboole_0
      | ~ r2_hidden(A_175,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_901,c_8])).

tff(c_912,plain,
    ( k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_48,c_907])).

tff(c_913,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_912])).

tff(c_920,plain,(
    ! [A_179,B_180] : k1_setfam_1(k2_tarski(A_179,B_180)) = k3_xboole_0(A_179,B_180) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_929,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = k1_setfam_1(k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_920])).

tff(c_932,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_929])).

tff(c_962,plain,(
    ! [A_187,B_188] : k5_xboole_0(A_187,k3_xboole_0(A_187,B_188)) = k4_xboole_0(A_187,B_188) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_971,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_932,c_962])).

tff(c_977,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_971])).

tff(c_1115,plain,(
    ! [A_206,C_207,B_208] : k4_xboole_0(k2_zfmisc_1(A_206,C_207),k2_zfmisc_1(B_208,C_207)) = k2_zfmisc_1(k4_xboole_0(A_206,B_208),C_207) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1122,plain,(
    ! [B_208,C_207] : k2_zfmisc_1(k4_xboole_0(B_208,B_208),C_207) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1115,c_977])).

tff(c_1131,plain,(
    ! [C_207] : k2_zfmisc_1(k1_xboole_0,C_207) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_977,c_1122])).

tff(c_1190,plain,(
    ! [C_214,A_215,B_216] : k4_xboole_0(k2_zfmisc_1(C_214,A_215),k2_zfmisc_1(C_214,B_216)) = k2_zfmisc_1(C_214,k4_xboole_0(A_215,B_216)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_32,plain,(
    ! [A_41,C_43,B_42] : k4_xboole_0(k2_zfmisc_1(A_41,C_43),k2_zfmisc_1(B_42,C_43)) = k2_zfmisc_1(k4_xboole_0(A_41,B_42),C_43) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1197,plain,(
    ! [C_214,B_216] : k2_zfmisc_1(k4_xboole_0(C_214,C_214),B_216) = k2_zfmisc_1(C_214,k4_xboole_0(B_216,B_216)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1190,c_32])).

tff(c_1220,plain,(
    ! [C_214] : k2_zfmisc_1(C_214,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1131,c_977,c_977,c_1197])).

tff(c_1775,plain,(
    ! [B_262,A_263] :
      ( k2_relat_1(k5_relat_1(B_262,A_263)) = k2_relat_1(A_263)
      | ~ r1_tarski(k1_relat_1(A_263),k2_relat_1(B_262))
      | ~ v1_relat_1(B_262)
      | ~ v1_relat_1(A_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1781,plain,(
    ! [B_262] :
      ( k2_relat_1(k5_relat_1(B_262,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_262))
      | ~ v1_relat_1(B_262)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_1775])).

tff(c_1791,plain,(
    ! [B_264] :
      ( k2_relat_1(k5_relat_1(B_264,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_264) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_913,c_6,c_58,c_1781])).

tff(c_1809,plain,(
    ! [B_264] :
      ( k3_xboole_0(k5_relat_1(B_264,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(B_264,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(B_264,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_264,k1_xboole_0))
      | ~ v1_relat_1(B_264) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1791,c_52])).

tff(c_1853,plain,(
    ! [B_266] :
      ( k5_relat_1(B_266,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_266,k1_xboole_0))
      | ~ v1_relat_1(B_266) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1220,c_1809])).

tff(c_1860,plain,(
    ! [A_67] :
      ( k5_relat_1(A_67,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_67) ) ),
    inference(resolution,[status(thm)],[c_50,c_1853])).

tff(c_1866,plain,(
    ! [A_267] :
      ( k5_relat_1(A_267,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_267) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_913,c_1860])).

tff(c_1875,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_64,c_1866])).

tff(c_1882,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_894,c_1875])).

tff(c_1883,plain,(
    k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_912])).

tff(c_1889,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_1'(k1_xboole_0))) != k1_tarski('#skF_1'(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1883,c_36])).

tff(c_1901,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1883,c_1883,c_1889])).

tff(c_1987,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1983,c_1901])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:13:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.69  
% 3.49/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.69  %$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.49/1.69  
% 3.49/1.69  %Foreground sorts:
% 3.49/1.69  
% 3.49/1.69  
% 3.49/1.69  %Background operators:
% 3.49/1.69  
% 3.49/1.69  
% 3.49/1.69  %Foreground operators:
% 3.49/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.49/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.49/1.69  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.49/1.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.49/1.69  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.49/1.69  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.49/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.49/1.69  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.49/1.69  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.49/1.69  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.49/1.69  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.49/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.49/1.69  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.49/1.69  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.49/1.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.49/1.69  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.49/1.69  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.49/1.69  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.49/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.49/1.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.49/1.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.49/1.69  tff('#skF_4', type, '#skF_4': $i).
% 3.49/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.49/1.69  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.49/1.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.49/1.69  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.49/1.69  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.49/1.69  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.49/1.69  
% 3.81/1.71  tff(f_37, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.81/1.71  tff(f_68, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 3.81/1.71  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.81/1.71  tff(f_70, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.81/1.71  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.81/1.71  tff(f_66, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.81/1.71  tff(f_118, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 3.81/1.71  tff(f_80, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 3.81/1.71  tff(f_55, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.81/1.71  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.81/1.71  tff(f_86, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.81/1.71  tff(f_29, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.81/1.71  tff(f_61, axiom, (![A, B, C]: ((k2_zfmisc_1(k4_xboole_0(A, B), C) = k4_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k4_xboole_0(A, B)) = k4_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 3.81/1.71  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.81/1.71  tff(f_111, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.81/1.71  tff(f_99, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 3.81/1.71  tff(f_90, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 3.81/1.71  tff(f_108, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 3.81/1.71  tff(c_10, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.81/1.71  tff(c_40, plain, (![A_46]: (k1_setfam_1(k1_tarski(A_46))=A_46)), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.81/1.71  tff(c_12, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.81/1.71  tff(c_1918, plain, (![A_271, B_272]: (k1_setfam_1(k2_tarski(A_271, B_272))=k3_xboole_0(A_271, B_272))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.81/1.71  tff(c_1927, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=k1_setfam_1(k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1918])).
% 3.81/1.71  tff(c_1930, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1927])).
% 3.81/1.71  tff(c_1968, plain, (![A_280, B_281]: (k5_xboole_0(A_280, k3_xboole_0(A_280, B_281))=k4_xboole_0(A_280, B_281))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.81/1.71  tff(c_1977, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_1930, c_1968])).
% 3.81/1.71  tff(c_1983, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1977])).
% 3.81/1.71  tff(c_819, plain, (![A_164, B_165]: (k1_setfam_1(k2_tarski(A_164, B_165))=k3_xboole_0(A_164, B_165))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.81/1.71  tff(c_828, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=k1_setfam_1(k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_819])).
% 3.81/1.71  tff(c_831, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_828])).
% 3.81/1.71  tff(c_867, plain, (![A_169, B_170]: (k5_xboole_0(A_169, k3_xboole_0(A_169, B_170))=k4_xboole_0(A_169, B_170))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.81/1.71  tff(c_876, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_831, c_867])).
% 3.81/1.71  tff(c_882, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_876])).
% 3.81/1.71  tff(c_36, plain, (![B_45]: (k4_xboole_0(k1_tarski(B_45), k1_tarski(B_45))!=k1_tarski(B_45))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.81/1.71  tff(c_883, plain, (![B_45]: (k1_tarski(B_45)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_882, c_36])).
% 3.81/1.71  tff(c_62, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.81/1.71  tff(c_113, plain, (k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_62])).
% 3.81/1.71  tff(c_64, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.81/1.71  tff(c_48, plain, (![A_49]: (r2_hidden('#skF_1'(A_49), A_49) | v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.81/1.71  tff(c_115, plain, (![A_83, B_84]: (r1_tarski(k1_tarski(A_83), B_84) | ~r2_hidden(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.81/1.71  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.81/1.71  tff(c_121, plain, (![A_85]: (k1_tarski(A_85)=k1_xboole_0 | ~r2_hidden(A_85, k1_xboole_0))), inference(resolution, [status(thm)], [c_115, c_8])).
% 3.81/1.71  tff(c_126, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0 | v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_121])).
% 3.81/1.71  tff(c_127, plain, (v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_126])).
% 3.81/1.71  tff(c_50, plain, (![A_67, B_68]: (v1_relat_1(k5_relat_1(A_67, B_68)) | ~v1_relat_1(B_68) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.81/1.71  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.81/1.71  tff(c_137, plain, (![A_88, B_89]: (k1_setfam_1(k2_tarski(A_88, B_89))=k3_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.81/1.71  tff(c_146, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=k1_setfam_1(k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_137])).
% 3.81/1.71  tff(c_149, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_146])).
% 3.81/1.71  tff(c_176, plain, (![A_97, B_98]: (k5_xboole_0(A_97, k3_xboole_0(A_97, B_98))=k4_xboole_0(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.81/1.71  tff(c_185, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_149, c_176])).
% 3.81/1.71  tff(c_191, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_185])).
% 3.81/1.71  tff(c_324, plain, (![A_116, C_117, B_118]: (k4_xboole_0(k2_zfmisc_1(A_116, C_117), k2_zfmisc_1(B_118, C_117))=k2_zfmisc_1(k4_xboole_0(A_116, B_118), C_117))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.81/1.71  tff(c_331, plain, (![B_118, C_117]: (k2_zfmisc_1(k4_xboole_0(B_118, B_118), C_117)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_324, c_191])).
% 3.81/1.71  tff(c_340, plain, (![C_117]: (k2_zfmisc_1(k1_xboole_0, C_117)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_191, c_331])).
% 3.81/1.71  tff(c_6, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.81/1.71  tff(c_60, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.81/1.71  tff(c_58, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.81/1.71  tff(c_727, plain, (![A_152, B_153]: (k1_relat_1(k5_relat_1(A_152, B_153))=k1_relat_1(A_152) | ~r1_tarski(k2_relat_1(A_152), k1_relat_1(B_153)) | ~v1_relat_1(B_153) | ~v1_relat_1(A_152))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.81/1.71  tff(c_733, plain, (![B_153]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_153))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_153)) | ~v1_relat_1(B_153) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_58, c_727])).
% 3.81/1.71  tff(c_738, plain, (![B_154]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_154))=k1_xboole_0 | ~v1_relat_1(B_154))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_6, c_60, c_733])).
% 3.81/1.71  tff(c_52, plain, (![A_69]: (k3_xboole_0(A_69, k2_zfmisc_1(k1_relat_1(A_69), k2_relat_1(A_69)))=A_69 | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.81/1.71  tff(c_750, plain, (![B_154]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_154), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_154))))=k5_relat_1(k1_xboole_0, B_154) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_154)) | ~v1_relat_1(B_154))), inference(superposition, [status(thm), theory('equality')], [c_738, c_52])).
% 3.81/1.71  tff(c_758, plain, (![B_155]: (k5_relat_1(k1_xboole_0, B_155)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_155)) | ~v1_relat_1(B_155))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_340, c_750])).
% 3.81/1.71  tff(c_762, plain, (![B_68]: (k5_relat_1(k1_xboole_0, B_68)=k1_xboole_0 | ~v1_relat_1(B_68) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_50, c_758])).
% 3.81/1.71  tff(c_766, plain, (![B_156]: (k5_relat_1(k1_xboole_0, B_156)=k1_xboole_0 | ~v1_relat_1(B_156))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_762])).
% 3.81/1.71  tff(c_775, plain, (k5_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_64, c_766])).
% 3.81/1.71  tff(c_781, plain, $false, inference(negUnitSimplification, [status(thm)], [c_113, c_775])).
% 3.81/1.71  tff(c_782, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0), inference(splitRight, [status(thm)], [c_126])).
% 3.81/1.71  tff(c_893, plain, $false, inference(negUnitSimplification, [status(thm)], [c_883, c_782])).
% 3.81/1.71  tff(c_894, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_62])).
% 3.81/1.71  tff(c_901, plain, (![A_173, B_174]: (r1_tarski(k1_tarski(A_173), B_174) | ~r2_hidden(A_173, B_174))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.81/1.71  tff(c_907, plain, (![A_175]: (k1_tarski(A_175)=k1_xboole_0 | ~r2_hidden(A_175, k1_xboole_0))), inference(resolution, [status(thm)], [c_901, c_8])).
% 3.81/1.71  tff(c_912, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0 | v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_907])).
% 3.81/1.71  tff(c_913, plain, (v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_912])).
% 3.81/1.71  tff(c_920, plain, (![A_179, B_180]: (k1_setfam_1(k2_tarski(A_179, B_180))=k3_xboole_0(A_179, B_180))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.81/1.71  tff(c_929, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=k1_setfam_1(k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_920])).
% 3.81/1.71  tff(c_932, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_929])).
% 3.81/1.71  tff(c_962, plain, (![A_187, B_188]: (k5_xboole_0(A_187, k3_xboole_0(A_187, B_188))=k4_xboole_0(A_187, B_188))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.81/1.71  tff(c_971, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_932, c_962])).
% 3.81/1.71  tff(c_977, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_971])).
% 3.81/1.71  tff(c_1115, plain, (![A_206, C_207, B_208]: (k4_xboole_0(k2_zfmisc_1(A_206, C_207), k2_zfmisc_1(B_208, C_207))=k2_zfmisc_1(k4_xboole_0(A_206, B_208), C_207))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.81/1.71  tff(c_1122, plain, (![B_208, C_207]: (k2_zfmisc_1(k4_xboole_0(B_208, B_208), C_207)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1115, c_977])).
% 3.81/1.71  tff(c_1131, plain, (![C_207]: (k2_zfmisc_1(k1_xboole_0, C_207)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_977, c_1122])).
% 3.81/1.71  tff(c_1190, plain, (![C_214, A_215, B_216]: (k4_xboole_0(k2_zfmisc_1(C_214, A_215), k2_zfmisc_1(C_214, B_216))=k2_zfmisc_1(C_214, k4_xboole_0(A_215, B_216)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.81/1.71  tff(c_32, plain, (![A_41, C_43, B_42]: (k4_xboole_0(k2_zfmisc_1(A_41, C_43), k2_zfmisc_1(B_42, C_43))=k2_zfmisc_1(k4_xboole_0(A_41, B_42), C_43))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.81/1.71  tff(c_1197, plain, (![C_214, B_216]: (k2_zfmisc_1(k4_xboole_0(C_214, C_214), B_216)=k2_zfmisc_1(C_214, k4_xboole_0(B_216, B_216)))), inference(superposition, [status(thm), theory('equality')], [c_1190, c_32])).
% 3.81/1.71  tff(c_1220, plain, (![C_214]: (k2_zfmisc_1(C_214, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1131, c_977, c_977, c_1197])).
% 3.81/1.71  tff(c_1775, plain, (![B_262, A_263]: (k2_relat_1(k5_relat_1(B_262, A_263))=k2_relat_1(A_263) | ~r1_tarski(k1_relat_1(A_263), k2_relat_1(B_262)) | ~v1_relat_1(B_262) | ~v1_relat_1(A_263))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.81/1.71  tff(c_1781, plain, (![B_262]: (k2_relat_1(k5_relat_1(B_262, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_262)) | ~v1_relat_1(B_262) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_60, c_1775])).
% 3.81/1.71  tff(c_1791, plain, (![B_264]: (k2_relat_1(k5_relat_1(B_264, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_264))), inference(demodulation, [status(thm), theory('equality')], [c_913, c_6, c_58, c_1781])).
% 3.81/1.71  tff(c_1809, plain, (![B_264]: (k3_xboole_0(k5_relat_1(B_264, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(B_264, k1_xboole_0)), k1_xboole_0))=k5_relat_1(B_264, k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_264, k1_xboole_0)) | ~v1_relat_1(B_264))), inference(superposition, [status(thm), theory('equality')], [c_1791, c_52])).
% 3.81/1.71  tff(c_1853, plain, (![B_266]: (k5_relat_1(B_266, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_266, k1_xboole_0)) | ~v1_relat_1(B_266))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1220, c_1809])).
% 3.81/1.71  tff(c_1860, plain, (![A_67]: (k5_relat_1(A_67, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_67))), inference(resolution, [status(thm)], [c_50, c_1853])).
% 3.81/1.71  tff(c_1866, plain, (![A_267]: (k5_relat_1(A_267, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_267))), inference(demodulation, [status(thm), theory('equality')], [c_913, c_1860])).
% 3.81/1.71  tff(c_1875, plain, (k5_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_64, c_1866])).
% 3.81/1.71  tff(c_1882, plain, $false, inference(negUnitSimplification, [status(thm)], [c_894, c_1875])).
% 3.81/1.71  tff(c_1883, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0), inference(splitRight, [status(thm)], [c_912])).
% 3.81/1.71  tff(c_1889, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_1'(k1_xboole_0)))!=k1_tarski('#skF_1'(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1883, c_36])).
% 3.81/1.71  tff(c_1901, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1883, c_1883, c_1889])).
% 3.81/1.71  tff(c_1987, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1983, c_1901])).
% 3.81/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.81/1.71  
% 3.81/1.71  Inference rules
% 3.81/1.71  ----------------------
% 3.81/1.71  #Ref     : 2
% 3.81/1.71  #Sup     : 431
% 3.81/1.71  #Fact    : 0
% 3.81/1.71  #Define  : 0
% 3.81/1.71  #Split   : 3
% 3.81/1.71  #Chain   : 0
% 3.81/1.71  #Close   : 0
% 3.81/1.71  
% 3.81/1.71  Ordering : KBO
% 3.81/1.71  
% 3.81/1.71  Simplification rules
% 3.81/1.71  ----------------------
% 3.81/1.71  #Subsume      : 5
% 3.81/1.71  #Demod        : 433
% 3.81/1.71  #Tautology    : 304
% 3.81/1.71  #SimpNegUnit  : 10
% 3.81/1.71  #BackRed      : 18
% 3.81/1.71  
% 3.81/1.71  #Partial instantiations: 0
% 3.81/1.71  #Strategies tried      : 1
% 3.81/1.71  
% 3.81/1.71  Timing (in seconds)
% 3.81/1.71  ----------------------
% 3.81/1.71  Preprocessing        : 0.33
% 3.81/1.71  Parsing              : 0.17
% 3.81/1.71  CNF conversion       : 0.02
% 3.81/1.71  Main loop            : 0.53
% 3.81/1.71  Inferencing          : 0.20
% 3.81/1.71  Reduction            : 0.18
% 3.81/1.71  Demodulation         : 0.14
% 3.81/1.71  BG Simplification    : 0.03
% 3.81/1.71  Subsumption          : 0.08
% 3.81/1.71  Abstraction          : 0.03
% 3.81/1.71  MUC search           : 0.00
% 3.81/1.71  Cooper               : 0.00
% 3.81/1.71  Total                : 0.91
% 3.81/1.71  Index Insertion      : 0.00
% 3.81/1.71  Index Deletion       : 0.00
% 3.81/1.71  Index Matching       : 0.00
% 3.81/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
