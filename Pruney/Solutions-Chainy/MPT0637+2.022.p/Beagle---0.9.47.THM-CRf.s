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
% DateTime   : Thu Dec  3 10:03:27 EST 2020

% Result     : Theorem 8.08s
% Output     : CNFRefutation 8.08s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 454 expanded)
%              Number of leaves         :   35 ( 184 expanded)
%              Depth                    :   12
%              Number of atoms          :  102 ( 681 expanded)
%              Number of equality atoms :   62 ( 306 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_35,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_37,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_116,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_90,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_108,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k8_relat_1(A,C),B) = k8_relat_1(A,k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

tff(f_92,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_112,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_119,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_146,plain,(
    ! [A_60,B_61] : k1_setfam_1(k2_tarski(A_60,B_61)) = k3_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_161,plain,(
    ! [B_62,A_63] : k1_setfam_1(k2_tarski(B_62,A_63)) = k3_xboole_0(A_63,B_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_146])).

tff(c_10,plain,(
    ! [A_12,B_13] : k1_setfam_1(k2_tarski(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_167,plain,(
    ! [B_62,A_63] : k3_xboole_0(B_62,A_63) = k3_xboole_0(A_63,B_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_10])).

tff(c_12,plain,(
    ! [A_14] : v1_relat_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_332,plain,(
    ! [A_81,B_82] :
      ( k5_relat_1(k6_relat_1(A_81),B_82) = k7_relat_1(B_82,A_81)
      | ~ v1_relat_1(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_22,plain,(
    ! [B_26,A_25] :
      ( k5_relat_1(B_26,k6_relat_1(A_25)) = k8_relat_1(A_25,B_26)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_343,plain,(
    ! [A_25,A_81] :
      ( k8_relat_1(A_25,k6_relat_1(A_81)) = k7_relat_1(k6_relat_1(A_25),A_81)
      | ~ v1_relat_1(k6_relat_1(A_81))
      | ~ v1_relat_1(k6_relat_1(A_25)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_22])).

tff(c_376,plain,(
    ! [A_25,A_81] : k8_relat_1(A_25,k6_relat_1(A_81)) = k7_relat_1(k6_relat_1(A_25),A_81) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_343])).

tff(c_36,plain,(
    ! [A_38] : k2_relat_1(k6_relat_1(A_38)) = A_38 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_46,plain,(
    ! [A_44] :
      ( k5_relat_1(A_44,k6_relat_1(k2_relat_1(A_44))) = A_44
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_347,plain,(
    ! [A_81] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_81))),A_81) = k6_relat_1(A_81)
      | ~ v1_relat_1(k6_relat_1(A_81))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_81)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_46])).

tff(c_378,plain,(
    ! [A_81] : k7_relat_1(k6_relat_1(A_81),A_81) = k6_relat_1(A_81) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_36,c_347])).

tff(c_1289,plain,(
    ! [A_152,C_153,B_154] :
      ( k8_relat_1(A_152,k7_relat_1(C_153,B_154)) = k7_relat_1(k8_relat_1(A_152,C_153),B_154)
      | ~ v1_relat_1(C_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1321,plain,(
    ! [A_152,A_81] :
      ( k7_relat_1(k8_relat_1(A_152,k6_relat_1(A_81)),A_81) = k8_relat_1(A_152,k6_relat_1(A_81))
      | ~ v1_relat_1(k6_relat_1(A_81)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_1289])).

tff(c_1327,plain,(
    ! [A_152,A_81] : k7_relat_1(k7_relat_1(k6_relat_1(A_152),A_81),A_81) = k7_relat_1(k6_relat_1(A_152),A_81) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_376,c_376,c_1321])).

tff(c_1926,plain,(
    ! [B_179,C_180,A_181] :
      ( k7_relat_1(k5_relat_1(B_179,C_180),A_181) = k5_relat_1(k7_relat_1(B_179,A_181),C_180)
      | ~ v1_relat_1(C_180)
      | ~ v1_relat_1(B_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1980,plain,(
    ! [B_26,A_181,A_25] :
      ( k5_relat_1(k7_relat_1(B_26,A_181),k6_relat_1(A_25)) = k7_relat_1(k8_relat_1(A_25,B_26),A_181)
      | ~ v1_relat_1(k6_relat_1(A_25))
      | ~ v1_relat_1(B_26)
      | ~ v1_relat_1(B_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1926])).

tff(c_3752,plain,(
    ! [B_228,A_229,A_230] :
      ( k5_relat_1(k7_relat_1(B_228,A_229),k6_relat_1(A_230)) = k7_relat_1(k8_relat_1(A_230,B_228),A_229)
      | ~ v1_relat_1(B_228) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1980])).

tff(c_3808,plain,(
    ! [A_230,A_81] :
      ( k7_relat_1(k8_relat_1(A_230,k6_relat_1(A_81)),A_81) = k5_relat_1(k6_relat_1(A_81),k6_relat_1(A_230))
      | ~ v1_relat_1(k6_relat_1(A_81)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_3752])).

tff(c_3832,plain,(
    ! [A_81,A_230] : k5_relat_1(k6_relat_1(A_81),k6_relat_1(A_230)) = k7_relat_1(k6_relat_1(A_230),A_81) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1327,c_376,c_3808])).

tff(c_38,plain,(
    ! [A_39] : k4_relat_1(k6_relat_1(A_39)) = k6_relat_1(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1718,plain,(
    ! [B_169,A_170] :
      ( k5_relat_1(k4_relat_1(B_169),k4_relat_1(A_170)) = k4_relat_1(k5_relat_1(A_170,B_169))
      | ~ v1_relat_1(B_169)
      | ~ v1_relat_1(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1736,plain,(
    ! [B_169,A_39] :
      ( k5_relat_1(k4_relat_1(B_169),k6_relat_1(A_39)) = k4_relat_1(k5_relat_1(k6_relat_1(A_39),B_169))
      | ~ v1_relat_1(B_169)
      | ~ v1_relat_1(k6_relat_1(A_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1718])).

tff(c_2314,plain,(
    ! [B_190,A_191] :
      ( k5_relat_1(k4_relat_1(B_190),k6_relat_1(A_191)) = k4_relat_1(k5_relat_1(k6_relat_1(A_191),B_190))
      | ~ v1_relat_1(B_190) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1736])).

tff(c_2350,plain,(
    ! [A_191,A_39] :
      ( k4_relat_1(k5_relat_1(k6_relat_1(A_191),k6_relat_1(A_39))) = k5_relat_1(k6_relat_1(A_39),k6_relat_1(A_191))
      | ~ v1_relat_1(k6_relat_1(A_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2314])).

tff(c_2356,plain,(
    ! [A_191,A_39] : k4_relat_1(k5_relat_1(k6_relat_1(A_191),k6_relat_1(A_39))) = k5_relat_1(k6_relat_1(A_39),k6_relat_1(A_191)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2350])).

tff(c_12499,plain,(
    ! [A_39,A_191] : k4_relat_1(k7_relat_1(k6_relat_1(A_39),A_191)) = k7_relat_1(k6_relat_1(A_191),A_39) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3832,c_3832,c_2356])).

tff(c_34,plain,(
    ! [A_38] : k1_relat_1(k6_relat_1(A_38)) = A_38 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_469,plain,(
    ! [B_94,A_95] :
      ( k3_xboole_0(k1_relat_1(B_94),A_95) = k1_relat_1(k7_relat_1(B_94,A_95))
      | ~ v1_relat_1(B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_498,plain,(
    ! [A_38,A_95] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_38),A_95)) = k3_xboole_0(A_38,A_95)
      | ~ v1_relat_1(k6_relat_1(A_38)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_469])).

tff(c_502,plain,(
    ! [A_38,A_95] : k1_relat_1(k7_relat_1(k6_relat_1(A_38),A_95)) = k3_xboole_0(A_38,A_95) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_498])).

tff(c_1146,plain,(
    ! [C_146,A_147,B_148] :
      ( k7_relat_1(k7_relat_1(C_146,A_147),B_148) = k7_relat_1(C_146,k3_xboole_0(A_147,B_148))
      | ~ v1_relat_1(C_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1180,plain,(
    ! [A_81,B_148] :
      ( k7_relat_1(k6_relat_1(A_81),k3_xboole_0(A_81,B_148)) = k7_relat_1(k6_relat_1(A_81),B_148)
      | ~ v1_relat_1(k6_relat_1(A_81)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_1146])).

tff(c_1328,plain,(
    ! [A_155,B_156] : k7_relat_1(k6_relat_1(A_155),k3_xboole_0(A_155,B_156)) = k7_relat_1(k6_relat_1(A_155),B_156) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1180])).

tff(c_1357,plain,(
    ! [A_155,B_156] : k3_xboole_0(A_155,k3_xboole_0(A_155,B_156)) = k1_relat_1(k7_relat_1(k6_relat_1(A_155),B_156)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1328,c_502])).

tff(c_1403,plain,(
    ! [A_155,B_156] : k3_xboole_0(A_155,k3_xboole_0(A_155,B_156)) = k3_xboole_0(A_155,B_156) ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_1357])).

tff(c_1998,plain,(
    ! [B_182,A_183] : k7_relat_1(k6_relat_1(B_182),k3_xboole_0(A_183,B_182)) = k7_relat_1(k6_relat_1(B_182),A_183) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_1328])).

tff(c_2058,plain,(
    ! [A_155,B_156] : k7_relat_1(k6_relat_1(k3_xboole_0(A_155,B_156)),k3_xboole_0(A_155,B_156)) = k7_relat_1(k6_relat_1(k3_xboole_0(A_155,B_156)),A_155) ),
    inference(superposition,[status(thm),theory(equality)],[c_1403,c_1998])).

tff(c_2107,plain,(
    ! [A_155,B_156] : k7_relat_1(k6_relat_1(k3_xboole_0(A_155,B_156)),A_155) = k6_relat_1(k3_xboole_0(A_155,B_156)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_2058])).

tff(c_1186,plain,(
    ! [A_81,B_148] : k7_relat_1(k6_relat_1(A_81),k3_xboole_0(A_81,B_148)) = k7_relat_1(k6_relat_1(A_81),B_148) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1180])).

tff(c_12500,plain,(
    ! [A_358,A_359] : k4_relat_1(k7_relat_1(k6_relat_1(A_358),A_359)) = k7_relat_1(k6_relat_1(A_359),A_358) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3832,c_3832,c_2356])).

tff(c_12557,plain,(
    ! [A_81,B_148] : k7_relat_1(k6_relat_1(k3_xboole_0(A_81,B_148)),A_81) = k4_relat_1(k7_relat_1(k6_relat_1(A_81),B_148)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1186,c_12500])).

tff(c_12593,plain,(
    ! [B_148,A_81] : k7_relat_1(k6_relat_1(B_148),A_81) = k6_relat_1(k3_xboole_0(A_81,B_148)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12499,c_2107,c_12557])).

tff(c_52,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_357,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_52])).

tff(c_382,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_357])).

tff(c_12617,plain,(
    k6_relat_1(k3_xboole_0('#skF_2','#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12593,c_382])).

tff(c_12631,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_12617])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:15:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.08/2.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.08/2.85  
% 8.08/2.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.08/2.85  %$ r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 8.08/2.85  
% 8.08/2.85  %Foreground sorts:
% 8.08/2.85  
% 8.08/2.85  
% 8.08/2.85  %Background operators:
% 8.08/2.85  
% 8.08/2.85  
% 8.08/2.85  %Foreground operators:
% 8.08/2.85  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 8.08/2.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.08/2.85  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.08/2.85  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.08/2.85  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.08/2.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.08/2.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.08/2.85  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.08/2.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.08/2.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.08/2.85  tff('#skF_2', type, '#skF_2': $i).
% 8.08/2.85  tff('#skF_1', type, '#skF_1': $i).
% 8.08/2.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.08/2.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.08/2.85  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.08/2.85  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.08/2.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.08/2.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.08/2.85  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.08/2.85  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 8.08/2.85  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.08/2.85  
% 8.08/2.87  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 8.08/2.87  tff(f_35, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 8.08/2.87  tff(f_37, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 8.08/2.87  tff(f_116, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 8.08/2.87  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 8.08/2.87  tff(f_90, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 8.08/2.87  tff(f_108, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 8.08/2.87  tff(f_68, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k8_relat_1(A, C), B) = k8_relat_1(A, k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_relat_1)).
% 8.08/2.87  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_relat_1)).
% 8.08/2.87  tff(f_92, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_relat_1)).
% 8.08/2.87  tff(f_86, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 8.08/2.87  tff(f_112, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 8.08/2.87  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 8.08/2.87  tff(f_119, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 8.08/2.87  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.08/2.87  tff(c_146, plain, (![A_60, B_61]: (k1_setfam_1(k2_tarski(A_60, B_61))=k3_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.08/2.87  tff(c_161, plain, (![B_62, A_63]: (k1_setfam_1(k2_tarski(B_62, A_63))=k3_xboole_0(A_63, B_62))), inference(superposition, [status(thm), theory('equality')], [c_2, c_146])).
% 8.08/2.87  tff(c_10, plain, (![A_12, B_13]: (k1_setfam_1(k2_tarski(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.08/2.87  tff(c_167, plain, (![B_62, A_63]: (k3_xboole_0(B_62, A_63)=k3_xboole_0(A_63, B_62))), inference(superposition, [status(thm), theory('equality')], [c_161, c_10])).
% 8.08/2.87  tff(c_12, plain, (![A_14]: (v1_relat_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.08/2.87  tff(c_332, plain, (![A_81, B_82]: (k5_relat_1(k6_relat_1(A_81), B_82)=k7_relat_1(B_82, A_81) | ~v1_relat_1(B_82))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.08/2.87  tff(c_22, plain, (![B_26, A_25]: (k5_relat_1(B_26, k6_relat_1(A_25))=k8_relat_1(A_25, B_26) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.08/2.87  tff(c_343, plain, (![A_25, A_81]: (k8_relat_1(A_25, k6_relat_1(A_81))=k7_relat_1(k6_relat_1(A_25), A_81) | ~v1_relat_1(k6_relat_1(A_81)) | ~v1_relat_1(k6_relat_1(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_332, c_22])).
% 8.08/2.87  tff(c_376, plain, (![A_25, A_81]: (k8_relat_1(A_25, k6_relat_1(A_81))=k7_relat_1(k6_relat_1(A_25), A_81))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_343])).
% 8.08/2.87  tff(c_36, plain, (![A_38]: (k2_relat_1(k6_relat_1(A_38))=A_38)), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.08/2.87  tff(c_46, plain, (![A_44]: (k5_relat_1(A_44, k6_relat_1(k2_relat_1(A_44)))=A_44 | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.08/2.87  tff(c_347, plain, (![A_81]: (k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_81))), A_81)=k6_relat_1(A_81) | ~v1_relat_1(k6_relat_1(A_81)) | ~v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_81)))))), inference(superposition, [status(thm), theory('equality')], [c_332, c_46])).
% 8.08/2.87  tff(c_378, plain, (![A_81]: (k7_relat_1(k6_relat_1(A_81), A_81)=k6_relat_1(A_81))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_36, c_347])).
% 8.08/2.87  tff(c_1289, plain, (![A_152, C_153, B_154]: (k8_relat_1(A_152, k7_relat_1(C_153, B_154))=k7_relat_1(k8_relat_1(A_152, C_153), B_154) | ~v1_relat_1(C_153))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.08/2.87  tff(c_1321, plain, (![A_152, A_81]: (k7_relat_1(k8_relat_1(A_152, k6_relat_1(A_81)), A_81)=k8_relat_1(A_152, k6_relat_1(A_81)) | ~v1_relat_1(k6_relat_1(A_81)))), inference(superposition, [status(thm), theory('equality')], [c_378, c_1289])).
% 8.08/2.87  tff(c_1327, plain, (![A_152, A_81]: (k7_relat_1(k7_relat_1(k6_relat_1(A_152), A_81), A_81)=k7_relat_1(k6_relat_1(A_152), A_81))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_376, c_376, c_1321])).
% 8.08/2.87  tff(c_1926, plain, (![B_179, C_180, A_181]: (k7_relat_1(k5_relat_1(B_179, C_180), A_181)=k5_relat_1(k7_relat_1(B_179, A_181), C_180) | ~v1_relat_1(C_180) | ~v1_relat_1(B_179))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.08/2.87  tff(c_1980, plain, (![B_26, A_181, A_25]: (k5_relat_1(k7_relat_1(B_26, A_181), k6_relat_1(A_25))=k7_relat_1(k8_relat_1(A_25, B_26), A_181) | ~v1_relat_1(k6_relat_1(A_25)) | ~v1_relat_1(B_26) | ~v1_relat_1(B_26))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1926])).
% 8.08/2.87  tff(c_3752, plain, (![B_228, A_229, A_230]: (k5_relat_1(k7_relat_1(B_228, A_229), k6_relat_1(A_230))=k7_relat_1(k8_relat_1(A_230, B_228), A_229) | ~v1_relat_1(B_228))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1980])).
% 8.08/2.87  tff(c_3808, plain, (![A_230, A_81]: (k7_relat_1(k8_relat_1(A_230, k6_relat_1(A_81)), A_81)=k5_relat_1(k6_relat_1(A_81), k6_relat_1(A_230)) | ~v1_relat_1(k6_relat_1(A_81)))), inference(superposition, [status(thm), theory('equality')], [c_378, c_3752])).
% 8.08/2.87  tff(c_3832, plain, (![A_81, A_230]: (k5_relat_1(k6_relat_1(A_81), k6_relat_1(A_230))=k7_relat_1(k6_relat_1(A_230), A_81))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1327, c_376, c_3808])).
% 8.08/2.87  tff(c_38, plain, (![A_39]: (k4_relat_1(k6_relat_1(A_39))=k6_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.08/2.87  tff(c_1718, plain, (![B_169, A_170]: (k5_relat_1(k4_relat_1(B_169), k4_relat_1(A_170))=k4_relat_1(k5_relat_1(A_170, B_169)) | ~v1_relat_1(B_169) | ~v1_relat_1(A_170))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.08/2.87  tff(c_1736, plain, (![B_169, A_39]: (k5_relat_1(k4_relat_1(B_169), k6_relat_1(A_39))=k4_relat_1(k5_relat_1(k6_relat_1(A_39), B_169)) | ~v1_relat_1(B_169) | ~v1_relat_1(k6_relat_1(A_39)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1718])).
% 8.08/2.87  tff(c_2314, plain, (![B_190, A_191]: (k5_relat_1(k4_relat_1(B_190), k6_relat_1(A_191))=k4_relat_1(k5_relat_1(k6_relat_1(A_191), B_190)) | ~v1_relat_1(B_190))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1736])).
% 8.08/2.87  tff(c_2350, plain, (![A_191, A_39]: (k4_relat_1(k5_relat_1(k6_relat_1(A_191), k6_relat_1(A_39)))=k5_relat_1(k6_relat_1(A_39), k6_relat_1(A_191)) | ~v1_relat_1(k6_relat_1(A_39)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_2314])).
% 8.08/2.87  tff(c_2356, plain, (![A_191, A_39]: (k4_relat_1(k5_relat_1(k6_relat_1(A_191), k6_relat_1(A_39)))=k5_relat_1(k6_relat_1(A_39), k6_relat_1(A_191)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2350])).
% 8.08/2.87  tff(c_12499, plain, (![A_39, A_191]: (k4_relat_1(k7_relat_1(k6_relat_1(A_39), A_191))=k7_relat_1(k6_relat_1(A_191), A_39))), inference(demodulation, [status(thm), theory('equality')], [c_3832, c_3832, c_2356])).
% 8.08/2.87  tff(c_34, plain, (![A_38]: (k1_relat_1(k6_relat_1(A_38))=A_38)), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.08/2.87  tff(c_469, plain, (![B_94, A_95]: (k3_xboole_0(k1_relat_1(B_94), A_95)=k1_relat_1(k7_relat_1(B_94, A_95)) | ~v1_relat_1(B_94))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.08/2.87  tff(c_498, plain, (![A_38, A_95]: (k1_relat_1(k7_relat_1(k6_relat_1(A_38), A_95))=k3_xboole_0(A_38, A_95) | ~v1_relat_1(k6_relat_1(A_38)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_469])).
% 8.08/2.87  tff(c_502, plain, (![A_38, A_95]: (k1_relat_1(k7_relat_1(k6_relat_1(A_38), A_95))=k3_xboole_0(A_38, A_95))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_498])).
% 8.08/2.87  tff(c_1146, plain, (![C_146, A_147, B_148]: (k7_relat_1(k7_relat_1(C_146, A_147), B_148)=k7_relat_1(C_146, k3_xboole_0(A_147, B_148)) | ~v1_relat_1(C_146))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.08/2.87  tff(c_1180, plain, (![A_81, B_148]: (k7_relat_1(k6_relat_1(A_81), k3_xboole_0(A_81, B_148))=k7_relat_1(k6_relat_1(A_81), B_148) | ~v1_relat_1(k6_relat_1(A_81)))), inference(superposition, [status(thm), theory('equality')], [c_378, c_1146])).
% 8.08/2.87  tff(c_1328, plain, (![A_155, B_156]: (k7_relat_1(k6_relat_1(A_155), k3_xboole_0(A_155, B_156))=k7_relat_1(k6_relat_1(A_155), B_156))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1180])).
% 8.08/2.87  tff(c_1357, plain, (![A_155, B_156]: (k3_xboole_0(A_155, k3_xboole_0(A_155, B_156))=k1_relat_1(k7_relat_1(k6_relat_1(A_155), B_156)))), inference(superposition, [status(thm), theory('equality')], [c_1328, c_502])).
% 8.08/2.87  tff(c_1403, plain, (![A_155, B_156]: (k3_xboole_0(A_155, k3_xboole_0(A_155, B_156))=k3_xboole_0(A_155, B_156))), inference(demodulation, [status(thm), theory('equality')], [c_502, c_1357])).
% 8.08/2.87  tff(c_1998, plain, (![B_182, A_183]: (k7_relat_1(k6_relat_1(B_182), k3_xboole_0(A_183, B_182))=k7_relat_1(k6_relat_1(B_182), A_183))), inference(superposition, [status(thm), theory('equality')], [c_167, c_1328])).
% 8.08/2.87  tff(c_2058, plain, (![A_155, B_156]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_155, B_156)), k3_xboole_0(A_155, B_156))=k7_relat_1(k6_relat_1(k3_xboole_0(A_155, B_156)), A_155))), inference(superposition, [status(thm), theory('equality')], [c_1403, c_1998])).
% 8.08/2.87  tff(c_2107, plain, (![A_155, B_156]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_155, B_156)), A_155)=k6_relat_1(k3_xboole_0(A_155, B_156)))), inference(demodulation, [status(thm), theory('equality')], [c_378, c_2058])).
% 8.08/2.87  tff(c_1186, plain, (![A_81, B_148]: (k7_relat_1(k6_relat_1(A_81), k3_xboole_0(A_81, B_148))=k7_relat_1(k6_relat_1(A_81), B_148))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1180])).
% 8.08/2.87  tff(c_12500, plain, (![A_358, A_359]: (k4_relat_1(k7_relat_1(k6_relat_1(A_358), A_359))=k7_relat_1(k6_relat_1(A_359), A_358))), inference(demodulation, [status(thm), theory('equality')], [c_3832, c_3832, c_2356])).
% 8.08/2.87  tff(c_12557, plain, (![A_81, B_148]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_81, B_148)), A_81)=k4_relat_1(k7_relat_1(k6_relat_1(A_81), B_148)))), inference(superposition, [status(thm), theory('equality')], [c_1186, c_12500])).
% 8.08/2.87  tff(c_12593, plain, (![B_148, A_81]: (k7_relat_1(k6_relat_1(B_148), A_81)=k6_relat_1(k3_xboole_0(A_81, B_148)))), inference(demodulation, [status(thm), theory('equality')], [c_12499, c_2107, c_12557])).
% 8.08/2.87  tff(c_52, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.08/2.87  tff(c_357, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_332, c_52])).
% 8.08/2.87  tff(c_382, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_357])).
% 8.08/2.87  tff(c_12617, plain, (k6_relat_1(k3_xboole_0('#skF_2', '#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12593, c_382])).
% 8.08/2.87  tff(c_12631, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_167, c_12617])).
% 8.08/2.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.08/2.87  
% 8.08/2.87  Inference rules
% 8.08/2.87  ----------------------
% 8.08/2.87  #Ref     : 0
% 8.08/2.87  #Sup     : 3113
% 8.08/2.87  #Fact    : 0
% 8.08/2.87  #Define  : 0
% 8.08/2.87  #Split   : 1
% 8.08/2.87  #Chain   : 0
% 8.08/2.87  #Close   : 0
% 8.08/2.87  
% 8.08/2.87  Ordering : KBO
% 8.08/2.87  
% 8.08/2.87  Simplification rules
% 8.08/2.87  ----------------------
% 8.08/2.87  #Subsume      : 388
% 8.08/2.87  #Demod        : 3314
% 8.08/2.87  #Tautology    : 1396
% 8.08/2.87  #SimpNegUnit  : 0
% 8.08/2.87  #BackRed      : 25
% 8.08/2.87  
% 8.08/2.87  #Partial instantiations: 0
% 8.08/2.87  #Strategies tried      : 1
% 8.08/2.87  
% 8.08/2.87  Timing (in seconds)
% 8.08/2.87  ----------------------
% 8.08/2.87  Preprocessing        : 0.33
% 8.08/2.87  Parsing              : 0.18
% 8.08/2.87  CNF conversion       : 0.02
% 8.08/2.87  Main loop            : 1.79
% 8.08/2.87  Inferencing          : 0.48
% 8.08/2.87  Reduction            : 0.81
% 8.08/2.87  Demodulation         : 0.68
% 8.08/2.87  BG Simplification    : 0.07
% 8.08/2.87  Subsumption          : 0.32
% 8.08/2.87  Abstraction          : 0.10
% 8.08/2.87  MUC search           : 0.00
% 8.08/2.87  Cooper               : 0.00
% 8.08/2.87  Total                : 2.15
% 8.08/2.87  Index Insertion      : 0.00
% 8.08/2.87  Index Deletion       : 0.00
% 8.08/2.87  Index Matching       : 0.00
% 8.08/2.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
