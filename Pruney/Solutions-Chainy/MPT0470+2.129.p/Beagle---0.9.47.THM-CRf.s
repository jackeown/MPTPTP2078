%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:19 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 282 expanded)
%              Number of leaves         :   44 ( 114 expanded)
%              Depth                    :   11
%              Number of atoms          :  149 ( 412 expanded)
%              Number of equality atoms :   81 ( 224 expanded)
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

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k4_xboole_0(A,B),C) = k4_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k4_xboole_0(A,B)) = k4_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_111,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_99,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_108,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_12,plain,(
    ! [A_8] : k5_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1710,plain,(
    ! [A_255,B_256] : k5_xboole_0(A_255,k3_xboole_0(A_255,B_256)) = k4_xboole_0(A_255,B_256) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1722,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1710])).

tff(c_1725,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1722])).

tff(c_906,plain,(
    ! [A_170,B_171] : k5_xboole_0(A_170,k3_xboole_0(A_170,B_171)) = k4_xboole_0(A_170,B_171) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_918,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_906])).

tff(c_921,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_918])).

tff(c_62,plain,
    ( k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_123,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_64,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_48,plain,(
    ! [A_50] :
      ( r2_hidden('#skF_1'(A_50),A_50)
      | v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_126,plain,(
    ! [A_85,B_86] :
      ( r1_tarski(k1_tarski(A_85),B_86)
      | ~ r2_hidden(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_132,plain,(
    ! [A_87] :
      ( k1_tarski(A_87) = k1_xboole_0
      | ~ r2_hidden(A_87,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_126,c_10])).

tff(c_137,plain,
    ( k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_48,c_132])).

tff(c_147,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_50,plain,(
    ! [A_68,B_69] :
      ( v1_relat_1(k5_relat_1(A_68,B_69))
      | ~ v1_relat_1(B_69)
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_176,plain,(
    ! [A_98,B_99] : k5_xboole_0(A_98,k3_xboole_0(A_98,B_99)) = k4_xboole_0(A_98,B_99) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_188,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_176])).

tff(c_191,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_188])).

tff(c_324,plain,(
    ! [C_117,A_118,B_119] : k4_xboole_0(k2_zfmisc_1(C_117,A_118),k2_zfmisc_1(C_117,B_119)) = k2_zfmisc_1(C_117,k4_xboole_0(A_118,B_119)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_331,plain,(
    ! [C_117,B_119] : k2_zfmisc_1(C_117,k4_xboole_0(B_119,B_119)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_191])).

tff(c_340,plain,(
    ! [C_117] : k2_zfmisc_1(C_117,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_331])).

tff(c_361,plain,(
    ! [A_121,C_122,B_123] : k4_xboole_0(k2_zfmisc_1(A_121,C_122),k2_zfmisc_1(B_123,C_122)) = k2_zfmisc_1(k4_xboole_0(A_121,B_123),C_122) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_36,plain,(
    ! [C_45,A_43,B_44] : k4_xboole_0(k2_zfmisc_1(C_45,A_43),k2_zfmisc_1(C_45,B_44)) = k2_zfmisc_1(C_45,k4_xboole_0(A_43,B_44)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_368,plain,(
    ! [B_123,C_122] : k2_zfmisc_1(k4_xboole_0(B_123,B_123),C_122) = k2_zfmisc_1(B_123,k4_xboole_0(C_122,C_122)) ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_36])).

tff(c_391,plain,(
    ! [C_122] : k2_zfmisc_1(k1_xboole_0,C_122) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_191,c_191,c_368])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_60,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_58,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_785,plain,(
    ! [A_154,B_155] :
      ( k1_relat_1(k5_relat_1(A_154,B_155)) = k1_relat_1(A_154)
      | ~ r1_tarski(k2_relat_1(A_154),k1_relat_1(B_155))
      | ~ v1_relat_1(B_155)
      | ~ v1_relat_1(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_791,plain,(
    ! [B_155] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_155)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_155))
      | ~ v1_relat_1(B_155)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_785])).

tff(c_796,plain,(
    ! [B_156] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_156)) = k1_xboole_0
      | ~ v1_relat_1(B_156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_8,c_60,c_791])).

tff(c_52,plain,(
    ! [A_70] :
      ( k3_xboole_0(A_70,k2_zfmisc_1(k1_relat_1(A_70),k2_relat_1(A_70))) = A_70
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_808,plain,(
    ! [B_156] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_156),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_156)))) = k5_relat_1(k1_xboole_0,B_156)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_156))
      | ~ v1_relat_1(B_156) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_796,c_52])).

tff(c_816,plain,(
    ! [B_157] :
      ( k5_relat_1(k1_xboole_0,B_157) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_157))
      | ~ v1_relat_1(B_157) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_391,c_808])).

tff(c_820,plain,(
    ! [B_69] :
      ( k5_relat_1(k1_xboole_0,B_69) = k1_xboole_0
      | ~ v1_relat_1(B_69)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_50,c_816])).

tff(c_824,plain,(
    ! [B_158] :
      ( k5_relat_1(k1_xboole_0,B_158) = k1_xboole_0
      | ~ v1_relat_1(B_158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_820])).

tff(c_833,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_64,c_824])).

tff(c_839,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_833])).

tff(c_840,plain,(
    k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_38,plain,(
    ! [B_47] : k4_xboole_0(k1_tarski(B_47),k1_tarski(B_47)) != k1_tarski(B_47) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_873,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_1'(k1_xboole_0))) != k1_tarski('#skF_1'(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_840,c_38])).

tff(c_880,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_840,c_840,c_873])).

tff(c_925,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_921,c_880])).

tff(c_926,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_958,plain,(
    ! [A_182,B_183] :
      ( r1_tarski(k1_tarski(A_182),B_183)
      | ~ r2_hidden(A_182,B_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_968,plain,(
    ! [A_184] :
      ( k1_tarski(A_184) = k1_xboole_0
      | ~ r2_hidden(A_184,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_958,c_10])).

tff(c_973,plain,
    ( k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_48,c_968])).

tff(c_974,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_973])).

tff(c_984,plain,(
    ! [A_187,B_188] : k5_xboole_0(A_187,k3_xboole_0(A_187,B_188)) = k4_xboole_0(A_187,B_188) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_996,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_984])).

tff(c_999,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_996])).

tff(c_1137,plain,(
    ! [A_206,C_207,B_208] : k4_xboole_0(k2_zfmisc_1(A_206,C_207),k2_zfmisc_1(B_208,C_207)) = k2_zfmisc_1(k4_xboole_0(A_206,B_208),C_207) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1144,plain,(
    ! [B_208,C_207] : k2_zfmisc_1(k4_xboole_0(B_208,B_208),C_207) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1137,c_999])).

tff(c_1153,plain,(
    ! [C_207] : k2_zfmisc_1(k1_xboole_0,C_207) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_999,c_1144])).

tff(c_1212,plain,(
    ! [C_214,A_215,B_216] : k4_xboole_0(k2_zfmisc_1(C_214,A_215),k2_zfmisc_1(C_214,B_216)) = k2_zfmisc_1(C_214,k4_xboole_0(A_215,B_216)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_34,plain,(
    ! [A_43,C_45,B_44] : k4_xboole_0(k2_zfmisc_1(A_43,C_45),k2_zfmisc_1(B_44,C_45)) = k2_zfmisc_1(k4_xboole_0(A_43,B_44),C_45) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1219,plain,(
    ! [C_214,B_216] : k2_zfmisc_1(k4_xboole_0(C_214,C_214),B_216) = k2_zfmisc_1(C_214,k4_xboole_0(B_216,B_216)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1212,c_34])).

tff(c_1242,plain,(
    ! [C_214] : k2_zfmisc_1(C_214,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1153,c_999,c_999,c_1219])).

tff(c_1602,plain,(
    ! [B_245,A_246] :
      ( k2_relat_1(k5_relat_1(B_245,A_246)) = k2_relat_1(A_246)
      | ~ r1_tarski(k1_relat_1(A_246),k2_relat_1(B_245))
      | ~ v1_relat_1(B_245)
      | ~ v1_relat_1(A_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1605,plain,(
    ! [B_245] :
      ( k2_relat_1(k5_relat_1(B_245,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_245))
      | ~ v1_relat_1(B_245)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_1602])).

tff(c_1613,plain,(
    ! [B_247] :
      ( k2_relat_1(k5_relat_1(B_247,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_247) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_974,c_8,c_58,c_1605])).

tff(c_1625,plain,(
    ! [B_247] :
      ( k3_xboole_0(k5_relat_1(B_247,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(B_247,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(B_247,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_247,k1_xboole_0))
      | ~ v1_relat_1(B_247) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1613,c_52])).

tff(c_1633,plain,(
    ! [B_248] :
      ( k5_relat_1(B_248,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_248,k1_xboole_0))
      | ~ v1_relat_1(B_248) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1242,c_1625])).

tff(c_1637,plain,(
    ! [A_68] :
      ( k5_relat_1(A_68,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_68) ) ),
    inference(resolution,[status(thm)],[c_50,c_1633])).

tff(c_1641,plain,(
    ! [A_249] :
      ( k5_relat_1(A_249,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_249) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_974,c_1637])).

tff(c_1650,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_64,c_1641])).

tff(c_1656,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_926,c_1650])).

tff(c_1657,plain,(
    k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_973])).

tff(c_1674,plain,(
    k4_xboole_0(k1_tarski('#skF_1'(k1_xboole_0)),k1_xboole_0) != k1_tarski('#skF_1'(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1657,c_38])).

tff(c_1681,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1657,c_1657,c_1674])).

tff(c_1729,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1725,c_1681])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:31:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.34/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.55  
% 3.34/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.56  %$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.34/1.56  
% 3.34/1.56  %Foreground sorts:
% 3.34/1.56  
% 3.34/1.56  
% 3.34/1.56  %Background operators:
% 3.34/1.56  
% 3.34/1.56  
% 3.34/1.56  %Foreground operators:
% 3.34/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.34/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.34/1.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.34/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.34/1.56  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.34/1.56  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.34/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.34/1.56  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.34/1.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.34/1.56  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.34/1.56  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.34/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.34/1.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.34/1.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.34/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.34/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.34/1.56  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.34/1.56  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.34/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.34/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.34/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.34/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.34/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.34/1.56  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.34/1.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.34/1.56  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.34/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.34/1.56  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.34/1.56  
% 3.34/1.57  tff(f_39, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.34/1.57  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.34/1.57  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.34/1.57  tff(f_118, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 3.34/1.57  tff(f_80, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 3.34/1.57  tff(f_57, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.34/1.57  tff(f_37, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.34/1.57  tff(f_86, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.34/1.57  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.34/1.57  tff(f_63, axiom, (![A, B, C]: ((k2_zfmisc_1(k4_xboole_0(A, B), C) = k4_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k4_xboole_0(A, B)) = k4_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 3.34/1.57  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.34/1.57  tff(f_111, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.34/1.57  tff(f_99, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 3.34/1.57  tff(f_90, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 3.34/1.57  tff(f_68, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.34/1.57  tff(f_108, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 3.34/1.57  tff(c_12, plain, (![A_8]: (k5_xboole_0(A_8, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.34/1.57  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.34/1.57  tff(c_1710, plain, (![A_255, B_256]: (k5_xboole_0(A_255, k3_xboole_0(A_255, B_256))=k4_xboole_0(A_255, B_256))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.34/1.57  tff(c_1722, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1710])).
% 3.34/1.57  tff(c_1725, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1722])).
% 3.34/1.57  tff(c_906, plain, (![A_170, B_171]: (k5_xboole_0(A_170, k3_xboole_0(A_170, B_171))=k4_xboole_0(A_170, B_171))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.34/1.57  tff(c_918, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_906])).
% 3.34/1.57  tff(c_921, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_918])).
% 3.34/1.57  tff(c_62, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.34/1.57  tff(c_123, plain, (k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_62])).
% 3.34/1.57  tff(c_64, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.34/1.57  tff(c_48, plain, (![A_50]: (r2_hidden('#skF_1'(A_50), A_50) | v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.34/1.57  tff(c_126, plain, (![A_85, B_86]: (r1_tarski(k1_tarski(A_85), B_86) | ~r2_hidden(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.34/1.57  tff(c_10, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.34/1.57  tff(c_132, plain, (![A_87]: (k1_tarski(A_87)=k1_xboole_0 | ~r2_hidden(A_87, k1_xboole_0))), inference(resolution, [status(thm)], [c_126, c_10])).
% 3.34/1.57  tff(c_137, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0 | v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_132])).
% 3.34/1.57  tff(c_147, plain, (v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_137])).
% 3.34/1.57  tff(c_50, plain, (![A_68, B_69]: (v1_relat_1(k5_relat_1(A_68, B_69)) | ~v1_relat_1(B_69) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.34/1.57  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.34/1.57  tff(c_176, plain, (![A_98, B_99]: (k5_xboole_0(A_98, k3_xboole_0(A_98, B_99))=k4_xboole_0(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.34/1.57  tff(c_188, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_176])).
% 3.34/1.57  tff(c_191, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_188])).
% 3.34/1.57  tff(c_324, plain, (![C_117, A_118, B_119]: (k4_xboole_0(k2_zfmisc_1(C_117, A_118), k2_zfmisc_1(C_117, B_119))=k2_zfmisc_1(C_117, k4_xboole_0(A_118, B_119)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.34/1.57  tff(c_331, plain, (![C_117, B_119]: (k2_zfmisc_1(C_117, k4_xboole_0(B_119, B_119))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_324, c_191])).
% 3.34/1.57  tff(c_340, plain, (![C_117]: (k2_zfmisc_1(C_117, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_191, c_331])).
% 3.34/1.57  tff(c_361, plain, (![A_121, C_122, B_123]: (k4_xboole_0(k2_zfmisc_1(A_121, C_122), k2_zfmisc_1(B_123, C_122))=k2_zfmisc_1(k4_xboole_0(A_121, B_123), C_122))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.34/1.57  tff(c_36, plain, (![C_45, A_43, B_44]: (k4_xboole_0(k2_zfmisc_1(C_45, A_43), k2_zfmisc_1(C_45, B_44))=k2_zfmisc_1(C_45, k4_xboole_0(A_43, B_44)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.34/1.57  tff(c_368, plain, (![B_123, C_122]: (k2_zfmisc_1(k4_xboole_0(B_123, B_123), C_122)=k2_zfmisc_1(B_123, k4_xboole_0(C_122, C_122)))), inference(superposition, [status(thm), theory('equality')], [c_361, c_36])).
% 3.34/1.57  tff(c_391, plain, (![C_122]: (k2_zfmisc_1(k1_xboole_0, C_122)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_340, c_191, c_191, c_368])).
% 3.34/1.57  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.34/1.57  tff(c_60, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.34/1.57  tff(c_58, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.34/1.57  tff(c_785, plain, (![A_154, B_155]: (k1_relat_1(k5_relat_1(A_154, B_155))=k1_relat_1(A_154) | ~r1_tarski(k2_relat_1(A_154), k1_relat_1(B_155)) | ~v1_relat_1(B_155) | ~v1_relat_1(A_154))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.34/1.57  tff(c_791, plain, (![B_155]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_155))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_155)) | ~v1_relat_1(B_155) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_58, c_785])).
% 3.34/1.57  tff(c_796, plain, (![B_156]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_156))=k1_xboole_0 | ~v1_relat_1(B_156))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_8, c_60, c_791])).
% 3.34/1.57  tff(c_52, plain, (![A_70]: (k3_xboole_0(A_70, k2_zfmisc_1(k1_relat_1(A_70), k2_relat_1(A_70)))=A_70 | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.34/1.57  tff(c_808, plain, (![B_156]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_156), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_156))))=k5_relat_1(k1_xboole_0, B_156) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_156)) | ~v1_relat_1(B_156))), inference(superposition, [status(thm), theory('equality')], [c_796, c_52])).
% 3.34/1.57  tff(c_816, plain, (![B_157]: (k5_relat_1(k1_xboole_0, B_157)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_157)) | ~v1_relat_1(B_157))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_391, c_808])).
% 3.34/1.57  tff(c_820, plain, (![B_69]: (k5_relat_1(k1_xboole_0, B_69)=k1_xboole_0 | ~v1_relat_1(B_69) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_50, c_816])).
% 3.34/1.57  tff(c_824, plain, (![B_158]: (k5_relat_1(k1_xboole_0, B_158)=k1_xboole_0 | ~v1_relat_1(B_158))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_820])).
% 3.34/1.57  tff(c_833, plain, (k5_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_64, c_824])).
% 3.34/1.57  tff(c_839, plain, $false, inference(negUnitSimplification, [status(thm)], [c_123, c_833])).
% 3.34/1.57  tff(c_840, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0), inference(splitRight, [status(thm)], [c_137])).
% 3.34/1.57  tff(c_38, plain, (![B_47]: (k4_xboole_0(k1_tarski(B_47), k1_tarski(B_47))!=k1_tarski(B_47))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.34/1.57  tff(c_873, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_1'(k1_xboole_0)))!=k1_tarski('#skF_1'(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_840, c_38])).
% 3.34/1.57  tff(c_880, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_840, c_840, c_873])).
% 3.34/1.57  tff(c_925, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_921, c_880])).
% 3.34/1.57  tff(c_926, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_62])).
% 3.34/1.57  tff(c_958, plain, (![A_182, B_183]: (r1_tarski(k1_tarski(A_182), B_183) | ~r2_hidden(A_182, B_183))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.34/1.57  tff(c_968, plain, (![A_184]: (k1_tarski(A_184)=k1_xboole_0 | ~r2_hidden(A_184, k1_xboole_0))), inference(resolution, [status(thm)], [c_958, c_10])).
% 3.34/1.57  tff(c_973, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0 | v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_968])).
% 3.34/1.57  tff(c_974, plain, (v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_973])).
% 3.34/1.57  tff(c_984, plain, (![A_187, B_188]: (k5_xboole_0(A_187, k3_xboole_0(A_187, B_188))=k4_xboole_0(A_187, B_188))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.34/1.57  tff(c_996, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_984])).
% 3.34/1.57  tff(c_999, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_996])).
% 3.34/1.57  tff(c_1137, plain, (![A_206, C_207, B_208]: (k4_xboole_0(k2_zfmisc_1(A_206, C_207), k2_zfmisc_1(B_208, C_207))=k2_zfmisc_1(k4_xboole_0(A_206, B_208), C_207))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.34/1.57  tff(c_1144, plain, (![B_208, C_207]: (k2_zfmisc_1(k4_xboole_0(B_208, B_208), C_207)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1137, c_999])).
% 3.34/1.57  tff(c_1153, plain, (![C_207]: (k2_zfmisc_1(k1_xboole_0, C_207)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_999, c_1144])).
% 3.34/1.57  tff(c_1212, plain, (![C_214, A_215, B_216]: (k4_xboole_0(k2_zfmisc_1(C_214, A_215), k2_zfmisc_1(C_214, B_216))=k2_zfmisc_1(C_214, k4_xboole_0(A_215, B_216)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.34/1.57  tff(c_34, plain, (![A_43, C_45, B_44]: (k4_xboole_0(k2_zfmisc_1(A_43, C_45), k2_zfmisc_1(B_44, C_45))=k2_zfmisc_1(k4_xboole_0(A_43, B_44), C_45))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.34/1.57  tff(c_1219, plain, (![C_214, B_216]: (k2_zfmisc_1(k4_xboole_0(C_214, C_214), B_216)=k2_zfmisc_1(C_214, k4_xboole_0(B_216, B_216)))), inference(superposition, [status(thm), theory('equality')], [c_1212, c_34])).
% 3.34/1.57  tff(c_1242, plain, (![C_214]: (k2_zfmisc_1(C_214, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1153, c_999, c_999, c_1219])).
% 3.34/1.57  tff(c_1602, plain, (![B_245, A_246]: (k2_relat_1(k5_relat_1(B_245, A_246))=k2_relat_1(A_246) | ~r1_tarski(k1_relat_1(A_246), k2_relat_1(B_245)) | ~v1_relat_1(B_245) | ~v1_relat_1(A_246))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.34/1.57  tff(c_1605, plain, (![B_245]: (k2_relat_1(k5_relat_1(B_245, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_245)) | ~v1_relat_1(B_245) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_60, c_1602])).
% 3.34/1.57  tff(c_1613, plain, (![B_247]: (k2_relat_1(k5_relat_1(B_247, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_247))), inference(demodulation, [status(thm), theory('equality')], [c_974, c_8, c_58, c_1605])).
% 3.34/1.57  tff(c_1625, plain, (![B_247]: (k3_xboole_0(k5_relat_1(B_247, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(B_247, k1_xboole_0)), k1_xboole_0))=k5_relat_1(B_247, k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_247, k1_xboole_0)) | ~v1_relat_1(B_247))), inference(superposition, [status(thm), theory('equality')], [c_1613, c_52])).
% 3.34/1.57  tff(c_1633, plain, (![B_248]: (k5_relat_1(B_248, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_248, k1_xboole_0)) | ~v1_relat_1(B_248))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1242, c_1625])).
% 3.34/1.57  tff(c_1637, plain, (![A_68]: (k5_relat_1(A_68, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_68))), inference(resolution, [status(thm)], [c_50, c_1633])).
% 3.34/1.57  tff(c_1641, plain, (![A_249]: (k5_relat_1(A_249, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_249))), inference(demodulation, [status(thm), theory('equality')], [c_974, c_1637])).
% 3.34/1.57  tff(c_1650, plain, (k5_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_64, c_1641])).
% 3.34/1.57  tff(c_1656, plain, $false, inference(negUnitSimplification, [status(thm)], [c_926, c_1650])).
% 3.34/1.57  tff(c_1657, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0), inference(splitRight, [status(thm)], [c_973])).
% 3.34/1.57  tff(c_1674, plain, (k4_xboole_0(k1_tarski('#skF_1'(k1_xboole_0)), k1_xboole_0)!=k1_tarski('#skF_1'(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1657, c_38])).
% 3.34/1.57  tff(c_1681, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1657, c_1657, c_1674])).
% 3.34/1.57  tff(c_1729, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1725, c_1681])).
% 3.34/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.57  
% 3.34/1.57  Inference rules
% 3.34/1.57  ----------------------
% 3.34/1.57  #Ref     : 2
% 3.34/1.57  #Sup     : 380
% 3.34/1.57  #Fact    : 0
% 3.34/1.57  #Define  : 0
% 3.34/1.57  #Split   : 3
% 3.34/1.57  #Chain   : 0
% 3.34/1.57  #Close   : 0
% 3.34/1.57  
% 3.34/1.57  Ordering : KBO
% 3.34/1.57  
% 3.34/1.57  Simplification rules
% 3.34/1.57  ----------------------
% 3.34/1.57  #Subsume      : 5
% 3.34/1.57  #Demod        : 366
% 3.34/1.57  #Tautology    : 255
% 3.34/1.57  #SimpNegUnit  : 9
% 3.34/1.57  #BackRed      : 15
% 3.34/1.57  
% 3.34/1.57  #Partial instantiations: 0
% 3.34/1.57  #Strategies tried      : 1
% 3.34/1.57  
% 3.34/1.57  Timing (in seconds)
% 3.34/1.57  ----------------------
% 3.34/1.58  Preprocessing        : 0.34
% 3.34/1.58  Parsing              : 0.18
% 3.34/1.58  CNF conversion       : 0.02
% 3.34/1.58  Main loop            : 0.46
% 3.34/1.58  Inferencing          : 0.17
% 3.34/1.58  Reduction            : 0.16
% 3.34/1.58  Demodulation         : 0.12
% 3.34/1.58  BG Simplification    : 0.03
% 3.34/1.58  Subsumption          : 0.06
% 3.34/1.58  Abstraction          : 0.03
% 3.34/1.58  MUC search           : 0.00
% 3.34/1.58  Cooper               : 0.00
% 3.34/1.58  Total                : 0.83
% 3.34/1.58  Index Insertion      : 0.00
% 3.34/1.58  Index Deletion       : 0.00
% 3.34/1.58  Index Matching       : 0.00
% 3.34/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
