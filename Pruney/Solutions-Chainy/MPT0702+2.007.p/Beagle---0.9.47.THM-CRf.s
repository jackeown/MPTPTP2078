%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:03 EST 2020

% Result     : Theorem 36.20s
% Output     : CNFRefutation 36.20s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 523 expanded)
%              Number of leaves         :   55 ( 204 expanded)
%              Depth                    :   16
%              Number of atoms          :  159 ( 575 expanded)
%              Number of equality atoms :  117 ( 481 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_49,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_243,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
            & r1_tarski(A,k1_relat_1(C))
            & v2_funct_1(C) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_77,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_61,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_69,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_91,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_189,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_224,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_205,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_89,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] : k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k4_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_701,plain,(
    ! [A_177,B_178] :
      ( r1_tarski(A_177,B_178)
      | k4_xboole_0(A_177,B_178) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_150,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_713,plain,(
    k4_xboole_0('#skF_5','#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_701,c_150])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3877,plain,(
    ! [A_326,B_327,C_328] : k4_xboole_0(k3_xboole_0(A_326,B_327),C_328) = k3_xboole_0(A_326,k4_xboole_0(B_327,C_328)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_3966,plain,(
    ! [A_5,C_328] : k3_xboole_0(A_5,k4_xboole_0(A_5,C_328)) = k4_xboole_0(A_5,C_328) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_3877])).

tff(c_207,plain,(
    ! [B_132,A_133] : k2_xboole_0(B_132,A_133) = k2_xboole_0(A_133,B_132) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ! [A_23] : k2_xboole_0(A_23,k1_xboole_0) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_223,plain,(
    ! [A_133] : k2_xboole_0(k1_xboole_0,A_133) = A_133 ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_24])).

tff(c_346,plain,(
    ! [A_143,B_144] : k3_xboole_0(A_143,k2_xboole_0(A_143,B_144)) = A_143 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_355,plain,(
    ! [A_133] : k3_xboole_0(k1_xboole_0,A_133) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_346])).

tff(c_1425,plain,(
    ! [A_226,B_227] : k5_xboole_0(A_226,k3_xboole_0(A_226,B_227)) = k4_xboole_0(A_226,B_227) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,(
    ! [A_28] : k4_xboole_0(A_28,k1_xboole_0) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_875,plain,(
    ! [A_196,B_197] : k5_xboole_0(A_196,k4_xboole_0(B_197,A_196)) = k2_xboole_0(A_196,B_197) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_908,plain,(
    ! [A_28] : k5_xboole_0(k1_xboole_0,A_28) = k2_xboole_0(k1_xboole_0,A_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_875])).

tff(c_916,plain,(
    ! [A_28] : k5_xboole_0(k1_xboole_0,A_28) = A_28 ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_908])).

tff(c_1432,plain,(
    ! [B_227] : k4_xboole_0(k1_xboole_0,B_227) = k3_xboole_0(k1_xboole_0,B_227) ),
    inference(superposition,[status(thm),theory(equality)],[c_1425,c_916])).

tff(c_1471,plain,(
    ! [B_227] : k4_xboole_0(k1_xboole_0,B_227) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_355,c_1432])).

tff(c_1006,plain,(
    ! [A_201,B_202] : k4_xboole_0(k2_xboole_0(A_201,B_202),B_202) = k4_xboole_0(A_201,B_202) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1031,plain,(
    ! [A_133] : k4_xboole_0(k1_xboole_0,A_133) = k4_xboole_0(A_133,A_133) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_1006])).

tff(c_1481,plain,(
    ! [A_133] : k4_xboole_0(A_133,A_133) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1471,c_1031])).

tff(c_1469,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1425])).

tff(c_1599,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1481,c_1469])).

tff(c_160,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_158,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_152,plain,(
    v2_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_126,plain,(
    ! [A_109,B_110] : k6_subset_1(A_109,B_110) = k4_xboole_0(A_109,B_110) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_146,plain,(
    ! [C_121,A_119,B_120] :
      ( k6_subset_1(k9_relat_1(C_121,A_119),k9_relat_1(C_121,B_120)) = k9_relat_1(C_121,k6_subset_1(A_119,B_120))
      | ~ v2_funct_1(C_121)
      | ~ v1_funct_1(C_121)
      | ~ v1_relat_1(C_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_16719,plain,(
    ! [C_549,A_550,B_551] :
      ( k4_xboole_0(k9_relat_1(C_549,A_550),k9_relat_1(C_549,B_551)) = k9_relat_1(C_549,k4_xboole_0(A_550,B_551))
      | ~ v2_funct_1(C_549)
      | ~ v1_funct_1(C_549)
      | ~ v1_relat_1(C_549) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_126,c_146])).

tff(c_156,plain,(
    r1_tarski(k9_relat_1('#skF_7','#skF_5'),k9_relat_1('#skF_7','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_555,plain,(
    ! [A_168,B_169] :
      ( k4_xboole_0(A_168,B_169) = k1_xboole_0
      | ~ r1_tarski(A_168,B_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_597,plain,(
    k4_xboole_0(k9_relat_1('#skF_7','#skF_5'),k9_relat_1('#skF_7','#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_156,c_555])).

tff(c_16855,plain,
    ( k9_relat_1('#skF_7',k4_xboole_0('#skF_5','#skF_6')) = k1_xboole_0
    | ~ v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_16719,c_597])).

tff(c_16898,plain,(
    k9_relat_1('#skF_7',k4_xboole_0('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_158,c_152,c_16855])).

tff(c_154,plain,(
    r1_tarski('#skF_5',k1_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_600,plain,(
    ! [A_170,B_171] :
      ( k2_xboole_0(A_170,B_171) = B_171
      | ~ r1_tarski(A_170,B_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_647,plain,(
    k2_xboole_0('#skF_5',k1_relat_1('#skF_7')) = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_154,c_600])).

tff(c_26,plain,(
    ! [A_24,B_25] : k3_xboole_0(A_24,k2_xboole_0(A_24,B_25)) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_665,plain,(
    k3_xboole_0('#skF_5',k1_relat_1('#skF_7')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_647,c_26])).

tff(c_6108,plain,(
    ! [B_362,A_363] :
      ( r1_xboole_0(k1_relat_1(B_362),A_363)
      | k9_relat_1(B_362,A_363) != k1_xboole_0
      | ~ v1_relat_1(B_362) ) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_32,plain,(
    ! [A_29,B_30] : k4_xboole_0(k2_xboole_0(A_29,B_30),B_30) = k4_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_42,plain,(
    ! [A_42,B_43] :
      ( k4_xboole_0(k2_xboole_0(A_42,B_43),B_43) = A_42
      | ~ r1_xboole_0(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_162,plain,(
    ! [A_42,B_43] :
      ( k4_xboole_0(A_42,B_43) = A_42
      | ~ r1_xboole_0(A_42,B_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_42])).

tff(c_96500,plain,(
    ! [B_1126,A_1127] :
      ( k4_xboole_0(k1_relat_1(B_1126),A_1127) = k1_relat_1(B_1126)
      | k9_relat_1(B_1126,A_1127) != k1_xboole_0
      | ~ v1_relat_1(B_1126) ) ),
    inference(resolution,[status(thm)],[c_6108,c_162])).

tff(c_3941,plain,(
    ! [C_328] : k3_xboole_0('#skF_5',k4_xboole_0(k1_relat_1('#skF_7'),C_328)) = k4_xboole_0('#skF_5',C_328) ),
    inference(superposition,[status(thm),theory(equality)],[c_665,c_3877])).

tff(c_96874,plain,(
    ! [A_1127] :
      ( k4_xboole_0('#skF_5',A_1127) = k3_xboole_0('#skF_5',k1_relat_1('#skF_7'))
      | k9_relat_1('#skF_7',A_1127) != k1_xboole_0
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96500,c_3941])).

tff(c_135975,plain,(
    ! [A_1368] :
      ( k4_xboole_0('#skF_5',A_1368) = '#skF_5'
      | k9_relat_1('#skF_7',A_1368) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_665,c_96874])).

tff(c_135998,plain,(
    k4_xboole_0('#skF_5',k4_xboole_0('#skF_5','#skF_6')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_16898,c_135975])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_361,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,k2_xboole_0(A_1,B_2)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_346])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    ! [A_48,B_49] : k5_xboole_0(A_48,k4_xboole_0(B_49,A_48)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2237,plain,(
    ! [A_256,B_257] : k4_xboole_0(k2_xboole_0(A_256,B_257),A_256) = k4_xboole_0(B_257,A_256) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1006])).

tff(c_2253,plain,(
    ! [A_256,B_257] : k5_xboole_0(A_256,k4_xboole_0(B_257,A_256)) = k2_xboole_0(A_256,k2_xboole_0(A_256,B_257)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2237,c_48])).

tff(c_2311,plain,(
    ! [A_256,B_257] : k2_xboole_0(A_256,k2_xboole_0(A_256,B_257)) = k2_xboole_0(A_256,B_257) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2253])).

tff(c_1037,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),A_1) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1006])).

tff(c_2985,plain,(
    ! [A_292,B_293] : k4_xboole_0(k2_xboole_0(A_292,B_293),k3_xboole_0(A_292,B_293)) = k5_xboole_0(A_292,B_293) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3066,plain,(
    ! [A_24,B_25] : k4_xboole_0(k2_xboole_0(A_24,k2_xboole_0(A_24,B_25)),A_24) = k5_xboole_0(A_24,k2_xboole_0(A_24,B_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2985])).

tff(c_3109,plain,(
    ! [A_24,B_25] : k5_xboole_0(A_24,k2_xboole_0(A_24,B_25)) = k4_xboole_0(B_25,A_24) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1037,c_1037,c_3066])).

tff(c_4641,plain,(
    ! [A_342,B_343] : k5_xboole_0(k5_xboole_0(A_342,B_343),k2_xboole_0(A_342,B_343)) = k3_xboole_0(A_342,B_343) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4680,plain,(
    ! [B_25,A_24] : k5_xboole_0(k4_xboole_0(B_25,A_24),k2_xboole_0(A_24,k2_xboole_0(A_24,B_25))) = k3_xboole_0(A_24,k2_xboole_0(A_24,B_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3109,c_4641])).

tff(c_4771,plain,(
    ! [B_344,A_345] : k5_xboole_0(k4_xboole_0(B_344,A_345),k2_xboole_0(A_345,B_344)) = A_345 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2311,c_26,c_4680])).

tff(c_4879,plain,(
    ! [B_2,A_1] : k5_xboole_0(k4_xboole_0(B_2,A_1),k2_xboole_0(B_2,A_1)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4771])).

tff(c_7155,plain,(
    ! [A_390,B_391,C_392] : k4_xboole_0(k3_xboole_0(A_390,B_391),k3_xboole_0(C_392,B_391)) = k3_xboole_0(k4_xboole_0(A_390,C_392),B_391) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_7326,plain,(
    ! [A_5,C_392] : k4_xboole_0(A_5,k3_xboole_0(C_392,A_5)) = k3_xboole_0(k4_xboole_0(A_5,C_392),A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_7155])).

tff(c_7355,plain,(
    ! [A_5,C_392] : k4_xboole_0(A_5,k3_xboole_0(C_392,A_5)) = k4_xboole_0(A_5,C_392) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3966,c_4,c_7326])).

tff(c_3078,plain,(
    ! [B_2,A_1] : k4_xboole_0(k2_xboole_0(B_2,A_1),k3_xboole_0(A_1,B_2)) = k5_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2985])).

tff(c_41691,plain,(
    ! [A_767,B_768,C_769] : k3_xboole_0(A_767,k4_xboole_0(k2_xboole_0(A_767,B_768),C_769)) = k4_xboole_0(A_767,C_769) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_3877])).

tff(c_41825,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k3_xboole_0(B_2,k5_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3078,c_41691])).

tff(c_42328,plain,(
    ! [B_772,A_773] : k3_xboole_0(B_772,k5_xboole_0(A_773,B_772)) = k4_xboole_0(B_772,A_773) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7355,c_41825])).

tff(c_42490,plain,(
    ! [B_2,A_1] : k4_xboole_0(k2_xboole_0(B_2,A_1),k4_xboole_0(B_2,A_1)) = k3_xboole_0(k2_xboole_0(B_2,A_1),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_4879,c_42328])).

tff(c_43378,plain,(
    ! [B_777,A_778] : k4_xboole_0(k2_xboole_0(B_777,A_778),k4_xboole_0(B_777,A_778)) = A_778 ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_4,c_42490])).

tff(c_3953,plain,(
    ! [A_24,B_25,C_328] : k3_xboole_0(A_24,k4_xboole_0(k2_xboole_0(A_24,B_25),C_328)) = k4_xboole_0(A_24,C_328) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_3877])).

tff(c_43390,plain,(
    ! [B_777,A_778] : k4_xboole_0(B_777,k4_xboole_0(B_777,A_778)) = k3_xboole_0(B_777,A_778) ),
    inference(superposition,[status(thm),theory(equality)],[c_43378,c_3953])).

tff(c_3069,plain,(
    ! [A_3,B_4] : k4_xboole_0(k2_xboole_0(A_3,B_4),k3_xboole_0(B_4,A_3)) = k5_xboole_0(A_3,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2985])).

tff(c_41822,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k3_xboole_0(B_4,A_3)) = k3_xboole_0(A_3,k5_xboole_0(A_3,B_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3069,c_41691])).

tff(c_42039,plain,(
    ! [A_3,B_4] : k3_xboole_0(A_3,k5_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7355,c_41822])).

tff(c_3973,plain,(
    ! [A_329,C_330] : k3_xboole_0(A_329,k4_xboole_0(A_329,C_330)) = k4_xboole_0(A_329,C_330) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_3877])).

tff(c_1466,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,k3_xboole_0(A_3,B_4)) = k4_xboole_0(B_4,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1425])).

tff(c_3991,plain,(
    ! [A_329,C_330] : k5_xboole_0(k4_xboole_0(A_329,C_330),k4_xboole_0(A_329,C_330)) = k4_xboole_0(k4_xboole_0(A_329,C_330),A_329) ),
    inference(superposition,[status(thm),theory(equality)],[c_3973,c_1466])).

tff(c_4083,plain,(
    ! [A_331,C_332] : k4_xboole_0(k4_xboole_0(A_331,C_332),A_331) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1599,c_3991])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | k4_xboole_0(A_12,B_13) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_728,plain,(
    ! [A_184,B_185] :
      ( k3_xboole_0(A_184,B_185) = A_184
      | ~ r1_tarski(A_184,B_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_769,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | k4_xboole_0(A_12,B_13) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_728])).

tff(c_2243,plain,(
    ! [A_256,B_257] :
      ( k3_xboole_0(k2_xboole_0(A_256,B_257),A_256) = k2_xboole_0(A_256,B_257)
      | k4_xboole_0(B_257,A_256) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2237,c_769])).

tff(c_2309,plain,(
    ! [A_256,B_257] :
      ( k2_xboole_0(A_256,B_257) = A_256
      | k4_xboole_0(B_257,A_256) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_4,c_2243])).

tff(c_4174,plain,(
    ! [A_331,C_332] : k2_xboole_0(A_331,k4_xboole_0(A_331,C_332)) = A_331 ),
    inference(superposition,[status(thm),theory(equality)],[c_4083,c_2309])).

tff(c_16,plain,(
    ! [A_14,B_15] : k4_xboole_0(k2_xboole_0(A_14,B_15),k3_xboole_0(A_14,B_15)) = k5_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16373,plain,(
    ! [A_547,B_548] : k4_xboole_0(k5_xboole_0(A_547,B_548),k2_xboole_0(A_547,B_548)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_4083])).

tff(c_16560,plain,(
    ! [A_331,C_332] : k4_xboole_0(k5_xboole_0(A_331,k4_xboole_0(A_331,C_332)),A_331) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4174,c_16373])).

tff(c_43949,plain,(
    ! [B_779,A_780] : k4_xboole_0(B_779,k4_xboole_0(B_779,A_780)) = k3_xboole_0(B_779,A_780) ),
    inference(superposition,[status(thm),theory(equality)],[c_43378,c_3953])).

tff(c_44233,plain,(
    ! [B_779,A_780] : k5_xboole_0(k4_xboole_0(B_779,A_780),k3_xboole_0(B_779,A_780)) = k2_xboole_0(k4_xboole_0(B_779,A_780),B_779) ),
    inference(superposition,[status(thm),theory(equality)],[c_43949,c_48])).

tff(c_83649,plain,(
    ! [B_1072,A_1073] : k5_xboole_0(k4_xboole_0(B_1072,A_1073),k3_xboole_0(B_1072,A_1073)) = B_1072 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4174,c_2,c_44233])).

tff(c_83934,plain,(
    ! [A_331,C_332] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(A_331,k4_xboole_0(A_331,C_332)),A_331)) = k5_xboole_0(A_331,k4_xboole_0(A_331,C_332)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16560,c_83649])).

tff(c_84218,plain,(
    ! [A_331,C_332] : k5_xboole_0(A_331,k4_xboole_0(A_331,C_332)) = k3_xboole_0(A_331,C_332) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43390,c_42039,c_916,c_4,c_83934])).

tff(c_136066,plain,(
    k3_xboole_0('#skF_5',k4_xboole_0('#skF_5','#skF_6')) = k5_xboole_0('#skF_5','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_135998,c_84218])).

tff(c_136343,plain,(
    k4_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3966,c_1599,c_136066])).

tff(c_136345,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_713,c_136343])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:45:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 36.20/26.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.20/26.66  
% 36.20/26.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.20/26.66  %$ r2_hidden > r1_xboole_0 > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 36.20/26.66  
% 36.20/26.66  %Foreground sorts:
% 36.20/26.66  
% 36.20/26.66  
% 36.20/26.66  %Background operators:
% 36.20/26.66  
% 36.20/26.66  
% 36.20/26.66  %Foreground operators:
% 36.20/26.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 36.20/26.66  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 36.20/26.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 36.20/26.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 36.20/26.66  tff(k1_tarski, type, k1_tarski: $i > $i).
% 36.20/26.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 36.20/26.66  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 36.20/26.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 36.20/26.66  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 36.20/26.66  tff('#skF_7', type, '#skF_7': $i).
% 36.20/26.66  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 36.20/26.66  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 36.20/26.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 36.20/26.66  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 36.20/26.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 36.20/26.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 36.20/26.66  tff('#skF_5', type, '#skF_5': $i).
% 36.20/26.66  tff('#skF_6', type, '#skF_6': $i).
% 36.20/26.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 36.20/26.66  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 36.20/26.66  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 36.20/26.66  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 36.20/26.66  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 36.20/26.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 36.20/26.66  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 36.20/26.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 36.20/26.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 36.20/26.66  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 36.20/26.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 36.20/26.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 36.20/26.66  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 36.20/26.66  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 36.20/26.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 36.20/26.66  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 36.20/26.66  
% 36.20/26.68  tff(f_49, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 36.20/26.68  tff(f_243, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t157_funct_1)).
% 36.20/26.68  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 36.20/26.68  tff(f_77, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 36.20/26.68  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 36.20/26.68  tff(f_61, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 36.20/26.68  tff(f_63, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 36.20/26.68  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 36.20/26.68  tff(f_69, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 36.20/26.68  tff(f_91, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 36.20/26.68  tff(f_71, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 36.20/26.68  tff(f_189, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 36.20/26.68  tff(f_224, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_funct_1)).
% 36.20/26.68  tff(f_59, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 36.20/26.68  tff(f_205, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 36.20/26.68  tff(f_85, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 36.20/26.68  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 36.20/26.68  tff(f_51, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l98_xboole_1)).
% 36.20/26.68  tff(f_89, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 36.20/26.68  tff(f_55, axiom, (![A, B, C]: (k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_xboole_1)).
% 36.20/26.68  tff(f_67, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 36.20/26.68  tff(c_701, plain, (![A_177, B_178]: (r1_tarski(A_177, B_178) | k4_xboole_0(A_177, B_178)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 36.20/26.68  tff(c_150, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_243])).
% 36.20/26.68  tff(c_713, plain, (k4_xboole_0('#skF_5', '#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_701, c_150])).
% 36.20/26.68  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 36.20/26.68  tff(c_3877, plain, (![A_326, B_327, C_328]: (k4_xboole_0(k3_xboole_0(A_326, B_327), C_328)=k3_xboole_0(A_326, k4_xboole_0(B_327, C_328)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 36.20/26.68  tff(c_3966, plain, (![A_5, C_328]: (k3_xboole_0(A_5, k4_xboole_0(A_5, C_328))=k4_xboole_0(A_5, C_328))), inference(superposition, [status(thm), theory('equality')], [c_6, c_3877])).
% 36.20/26.68  tff(c_207, plain, (![B_132, A_133]: (k2_xboole_0(B_132, A_133)=k2_xboole_0(A_133, B_132))), inference(cnfTransformation, [status(thm)], [f_27])).
% 36.20/26.68  tff(c_24, plain, (![A_23]: (k2_xboole_0(A_23, k1_xboole_0)=A_23)), inference(cnfTransformation, [status(thm)], [f_61])).
% 36.20/26.68  tff(c_223, plain, (![A_133]: (k2_xboole_0(k1_xboole_0, A_133)=A_133)), inference(superposition, [status(thm), theory('equality')], [c_207, c_24])).
% 36.20/26.68  tff(c_346, plain, (![A_143, B_144]: (k3_xboole_0(A_143, k2_xboole_0(A_143, B_144))=A_143)), inference(cnfTransformation, [status(thm)], [f_63])).
% 36.20/26.68  tff(c_355, plain, (![A_133]: (k3_xboole_0(k1_xboole_0, A_133)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_223, c_346])).
% 36.20/26.68  tff(c_1425, plain, (![A_226, B_227]: (k5_xboole_0(A_226, k3_xboole_0(A_226, B_227))=k4_xboole_0(A_226, B_227))), inference(cnfTransformation, [status(thm)], [f_53])).
% 36.20/26.68  tff(c_30, plain, (![A_28]: (k4_xboole_0(A_28, k1_xboole_0)=A_28)), inference(cnfTransformation, [status(thm)], [f_69])).
% 36.20/26.68  tff(c_875, plain, (![A_196, B_197]: (k5_xboole_0(A_196, k4_xboole_0(B_197, A_196))=k2_xboole_0(A_196, B_197))), inference(cnfTransformation, [status(thm)], [f_91])).
% 36.20/26.68  tff(c_908, plain, (![A_28]: (k5_xboole_0(k1_xboole_0, A_28)=k2_xboole_0(k1_xboole_0, A_28))), inference(superposition, [status(thm), theory('equality')], [c_30, c_875])).
% 36.20/26.68  tff(c_916, plain, (![A_28]: (k5_xboole_0(k1_xboole_0, A_28)=A_28)), inference(demodulation, [status(thm), theory('equality')], [c_223, c_908])).
% 36.20/26.68  tff(c_1432, plain, (![B_227]: (k4_xboole_0(k1_xboole_0, B_227)=k3_xboole_0(k1_xboole_0, B_227))), inference(superposition, [status(thm), theory('equality')], [c_1425, c_916])).
% 36.20/26.68  tff(c_1471, plain, (![B_227]: (k4_xboole_0(k1_xboole_0, B_227)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_355, c_1432])).
% 36.20/26.68  tff(c_1006, plain, (![A_201, B_202]: (k4_xboole_0(k2_xboole_0(A_201, B_202), B_202)=k4_xboole_0(A_201, B_202))), inference(cnfTransformation, [status(thm)], [f_71])).
% 36.20/26.68  tff(c_1031, plain, (![A_133]: (k4_xboole_0(k1_xboole_0, A_133)=k4_xboole_0(A_133, A_133))), inference(superposition, [status(thm), theory('equality')], [c_223, c_1006])).
% 36.20/26.68  tff(c_1481, plain, (![A_133]: (k4_xboole_0(A_133, A_133)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1471, c_1031])).
% 36.20/26.68  tff(c_1469, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1425])).
% 36.20/26.68  tff(c_1599, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1481, c_1469])).
% 36.20/26.68  tff(c_160, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_243])).
% 36.20/26.68  tff(c_158, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_243])).
% 36.20/26.68  tff(c_152, plain, (v2_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_243])).
% 36.20/26.68  tff(c_126, plain, (![A_109, B_110]: (k6_subset_1(A_109, B_110)=k4_xboole_0(A_109, B_110))), inference(cnfTransformation, [status(thm)], [f_189])).
% 36.20/26.68  tff(c_146, plain, (![C_121, A_119, B_120]: (k6_subset_1(k9_relat_1(C_121, A_119), k9_relat_1(C_121, B_120))=k9_relat_1(C_121, k6_subset_1(A_119, B_120)) | ~v2_funct_1(C_121) | ~v1_funct_1(C_121) | ~v1_relat_1(C_121))), inference(cnfTransformation, [status(thm)], [f_224])).
% 36.20/26.68  tff(c_16719, plain, (![C_549, A_550, B_551]: (k4_xboole_0(k9_relat_1(C_549, A_550), k9_relat_1(C_549, B_551))=k9_relat_1(C_549, k4_xboole_0(A_550, B_551)) | ~v2_funct_1(C_549) | ~v1_funct_1(C_549) | ~v1_relat_1(C_549))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_126, c_146])).
% 36.20/26.68  tff(c_156, plain, (r1_tarski(k9_relat_1('#skF_7', '#skF_5'), k9_relat_1('#skF_7', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_243])).
% 36.20/26.68  tff(c_555, plain, (![A_168, B_169]: (k4_xboole_0(A_168, B_169)=k1_xboole_0 | ~r1_tarski(A_168, B_169))), inference(cnfTransformation, [status(thm)], [f_49])).
% 36.20/26.68  tff(c_597, plain, (k4_xboole_0(k9_relat_1('#skF_7', '#skF_5'), k9_relat_1('#skF_7', '#skF_6'))=k1_xboole_0), inference(resolution, [status(thm)], [c_156, c_555])).
% 36.20/26.68  tff(c_16855, plain, (k9_relat_1('#skF_7', k4_xboole_0('#skF_5', '#skF_6'))=k1_xboole_0 | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_16719, c_597])).
% 36.20/26.68  tff(c_16898, plain, (k9_relat_1('#skF_7', k4_xboole_0('#skF_5', '#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_160, c_158, c_152, c_16855])).
% 36.20/26.68  tff(c_154, plain, (r1_tarski('#skF_5', k1_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_243])).
% 36.20/26.68  tff(c_600, plain, (![A_170, B_171]: (k2_xboole_0(A_170, B_171)=B_171 | ~r1_tarski(A_170, B_171))), inference(cnfTransformation, [status(thm)], [f_59])).
% 36.20/26.68  tff(c_647, plain, (k2_xboole_0('#skF_5', k1_relat_1('#skF_7'))=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_154, c_600])).
% 36.20/26.68  tff(c_26, plain, (![A_24, B_25]: (k3_xboole_0(A_24, k2_xboole_0(A_24, B_25))=A_24)), inference(cnfTransformation, [status(thm)], [f_63])).
% 36.20/26.68  tff(c_665, plain, (k3_xboole_0('#skF_5', k1_relat_1('#skF_7'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_647, c_26])).
% 36.20/26.68  tff(c_6108, plain, (![B_362, A_363]: (r1_xboole_0(k1_relat_1(B_362), A_363) | k9_relat_1(B_362, A_363)!=k1_xboole_0 | ~v1_relat_1(B_362))), inference(cnfTransformation, [status(thm)], [f_205])).
% 36.20/26.68  tff(c_32, plain, (![A_29, B_30]: (k4_xboole_0(k2_xboole_0(A_29, B_30), B_30)=k4_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_71])).
% 36.20/26.68  tff(c_42, plain, (![A_42, B_43]: (k4_xboole_0(k2_xboole_0(A_42, B_43), B_43)=A_42 | ~r1_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_85])).
% 36.20/26.68  tff(c_162, plain, (![A_42, B_43]: (k4_xboole_0(A_42, B_43)=A_42 | ~r1_xboole_0(A_42, B_43))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_42])).
% 36.20/26.68  tff(c_96500, plain, (![B_1126, A_1127]: (k4_xboole_0(k1_relat_1(B_1126), A_1127)=k1_relat_1(B_1126) | k9_relat_1(B_1126, A_1127)!=k1_xboole_0 | ~v1_relat_1(B_1126))), inference(resolution, [status(thm)], [c_6108, c_162])).
% 36.20/26.68  tff(c_3941, plain, (![C_328]: (k3_xboole_0('#skF_5', k4_xboole_0(k1_relat_1('#skF_7'), C_328))=k4_xboole_0('#skF_5', C_328))), inference(superposition, [status(thm), theory('equality')], [c_665, c_3877])).
% 36.20/26.68  tff(c_96874, plain, (![A_1127]: (k4_xboole_0('#skF_5', A_1127)=k3_xboole_0('#skF_5', k1_relat_1('#skF_7')) | k9_relat_1('#skF_7', A_1127)!=k1_xboole_0 | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_96500, c_3941])).
% 36.20/26.68  tff(c_135975, plain, (![A_1368]: (k4_xboole_0('#skF_5', A_1368)='#skF_5' | k9_relat_1('#skF_7', A_1368)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_160, c_665, c_96874])).
% 36.20/26.68  tff(c_135998, plain, (k4_xboole_0('#skF_5', k4_xboole_0('#skF_5', '#skF_6'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_16898, c_135975])).
% 36.20/26.68  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 36.20/26.68  tff(c_361, plain, (![B_2, A_1]: (k3_xboole_0(B_2, k2_xboole_0(A_1, B_2))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_346])).
% 36.20/26.68  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 36.20/26.68  tff(c_48, plain, (![A_48, B_49]: (k5_xboole_0(A_48, k4_xboole_0(B_49, A_48))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_91])).
% 36.20/26.68  tff(c_2237, plain, (![A_256, B_257]: (k4_xboole_0(k2_xboole_0(A_256, B_257), A_256)=k4_xboole_0(B_257, A_256))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1006])).
% 36.20/26.68  tff(c_2253, plain, (![A_256, B_257]: (k5_xboole_0(A_256, k4_xboole_0(B_257, A_256))=k2_xboole_0(A_256, k2_xboole_0(A_256, B_257)))), inference(superposition, [status(thm), theory('equality')], [c_2237, c_48])).
% 36.20/26.68  tff(c_2311, plain, (![A_256, B_257]: (k2_xboole_0(A_256, k2_xboole_0(A_256, B_257))=k2_xboole_0(A_256, B_257))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2253])).
% 36.20/26.68  tff(c_1037, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), A_1)=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1006])).
% 36.20/26.68  tff(c_2985, plain, (![A_292, B_293]: (k4_xboole_0(k2_xboole_0(A_292, B_293), k3_xboole_0(A_292, B_293))=k5_xboole_0(A_292, B_293))), inference(cnfTransformation, [status(thm)], [f_51])).
% 36.20/26.68  tff(c_3066, plain, (![A_24, B_25]: (k4_xboole_0(k2_xboole_0(A_24, k2_xboole_0(A_24, B_25)), A_24)=k5_xboole_0(A_24, k2_xboole_0(A_24, B_25)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_2985])).
% 36.20/26.68  tff(c_3109, plain, (![A_24, B_25]: (k5_xboole_0(A_24, k2_xboole_0(A_24, B_25))=k4_xboole_0(B_25, A_24))), inference(demodulation, [status(thm), theory('equality')], [c_1037, c_1037, c_3066])).
% 36.20/26.68  tff(c_4641, plain, (![A_342, B_343]: (k5_xboole_0(k5_xboole_0(A_342, B_343), k2_xboole_0(A_342, B_343))=k3_xboole_0(A_342, B_343))), inference(cnfTransformation, [status(thm)], [f_89])).
% 36.20/26.68  tff(c_4680, plain, (![B_25, A_24]: (k5_xboole_0(k4_xboole_0(B_25, A_24), k2_xboole_0(A_24, k2_xboole_0(A_24, B_25)))=k3_xboole_0(A_24, k2_xboole_0(A_24, B_25)))), inference(superposition, [status(thm), theory('equality')], [c_3109, c_4641])).
% 36.20/26.68  tff(c_4771, plain, (![B_344, A_345]: (k5_xboole_0(k4_xboole_0(B_344, A_345), k2_xboole_0(A_345, B_344))=A_345)), inference(demodulation, [status(thm), theory('equality')], [c_2311, c_26, c_4680])).
% 36.20/26.68  tff(c_4879, plain, (![B_2, A_1]: (k5_xboole_0(k4_xboole_0(B_2, A_1), k2_xboole_0(B_2, A_1))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_4771])).
% 36.20/26.68  tff(c_7155, plain, (![A_390, B_391, C_392]: (k4_xboole_0(k3_xboole_0(A_390, B_391), k3_xboole_0(C_392, B_391))=k3_xboole_0(k4_xboole_0(A_390, C_392), B_391))), inference(cnfTransformation, [status(thm)], [f_55])).
% 36.20/26.68  tff(c_7326, plain, (![A_5, C_392]: (k4_xboole_0(A_5, k3_xboole_0(C_392, A_5))=k3_xboole_0(k4_xboole_0(A_5, C_392), A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_7155])).
% 36.20/26.68  tff(c_7355, plain, (![A_5, C_392]: (k4_xboole_0(A_5, k3_xboole_0(C_392, A_5))=k4_xboole_0(A_5, C_392))), inference(demodulation, [status(thm), theory('equality')], [c_3966, c_4, c_7326])).
% 36.20/26.68  tff(c_3078, plain, (![B_2, A_1]: (k4_xboole_0(k2_xboole_0(B_2, A_1), k3_xboole_0(A_1, B_2))=k5_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2985])).
% 36.20/26.68  tff(c_41691, plain, (![A_767, B_768, C_769]: (k3_xboole_0(A_767, k4_xboole_0(k2_xboole_0(A_767, B_768), C_769))=k4_xboole_0(A_767, C_769))), inference(superposition, [status(thm), theory('equality')], [c_26, c_3877])).
% 36.20/26.68  tff(c_41825, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k3_xboole_0(B_2, k5_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_3078, c_41691])).
% 36.20/26.68  tff(c_42328, plain, (![B_772, A_773]: (k3_xboole_0(B_772, k5_xboole_0(A_773, B_772))=k4_xboole_0(B_772, A_773))), inference(demodulation, [status(thm), theory('equality')], [c_7355, c_41825])).
% 36.20/26.68  tff(c_42490, plain, (![B_2, A_1]: (k4_xboole_0(k2_xboole_0(B_2, A_1), k4_xboole_0(B_2, A_1))=k3_xboole_0(k2_xboole_0(B_2, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_4879, c_42328])).
% 36.20/26.68  tff(c_43378, plain, (![B_777, A_778]: (k4_xboole_0(k2_xboole_0(B_777, A_778), k4_xboole_0(B_777, A_778))=A_778)), inference(demodulation, [status(thm), theory('equality')], [c_361, c_4, c_42490])).
% 36.20/26.68  tff(c_3953, plain, (![A_24, B_25, C_328]: (k3_xboole_0(A_24, k4_xboole_0(k2_xboole_0(A_24, B_25), C_328))=k4_xboole_0(A_24, C_328))), inference(superposition, [status(thm), theory('equality')], [c_26, c_3877])).
% 36.20/26.68  tff(c_43390, plain, (![B_777, A_778]: (k4_xboole_0(B_777, k4_xboole_0(B_777, A_778))=k3_xboole_0(B_777, A_778))), inference(superposition, [status(thm), theory('equality')], [c_43378, c_3953])).
% 36.20/26.68  tff(c_3069, plain, (![A_3, B_4]: (k4_xboole_0(k2_xboole_0(A_3, B_4), k3_xboole_0(B_4, A_3))=k5_xboole_0(A_3, B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_2985])).
% 36.20/26.68  tff(c_41822, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k3_xboole_0(B_4, A_3))=k3_xboole_0(A_3, k5_xboole_0(A_3, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_3069, c_41691])).
% 36.20/26.68  tff(c_42039, plain, (![A_3, B_4]: (k3_xboole_0(A_3, k5_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(demodulation, [status(thm), theory('equality')], [c_7355, c_41822])).
% 36.20/26.68  tff(c_3973, plain, (![A_329, C_330]: (k3_xboole_0(A_329, k4_xboole_0(A_329, C_330))=k4_xboole_0(A_329, C_330))), inference(superposition, [status(thm), theory('equality')], [c_6, c_3877])).
% 36.20/26.68  tff(c_1466, plain, (![B_4, A_3]: (k5_xboole_0(B_4, k3_xboole_0(A_3, B_4))=k4_xboole_0(B_4, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1425])).
% 36.20/26.68  tff(c_3991, plain, (![A_329, C_330]: (k5_xboole_0(k4_xboole_0(A_329, C_330), k4_xboole_0(A_329, C_330))=k4_xboole_0(k4_xboole_0(A_329, C_330), A_329))), inference(superposition, [status(thm), theory('equality')], [c_3973, c_1466])).
% 36.20/26.68  tff(c_4083, plain, (![A_331, C_332]: (k4_xboole_0(k4_xboole_0(A_331, C_332), A_331)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1599, c_3991])).
% 36.20/26.68  tff(c_12, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | k4_xboole_0(A_12, B_13)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 36.20/26.68  tff(c_728, plain, (![A_184, B_185]: (k3_xboole_0(A_184, B_185)=A_184 | ~r1_tarski(A_184, B_185))), inference(cnfTransformation, [status(thm)], [f_67])).
% 36.20/26.68  tff(c_769, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | k4_xboole_0(A_12, B_13)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_728])).
% 36.20/26.68  tff(c_2243, plain, (![A_256, B_257]: (k3_xboole_0(k2_xboole_0(A_256, B_257), A_256)=k2_xboole_0(A_256, B_257) | k4_xboole_0(B_257, A_256)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2237, c_769])).
% 36.20/26.68  tff(c_2309, plain, (![A_256, B_257]: (k2_xboole_0(A_256, B_257)=A_256 | k4_xboole_0(B_257, A_256)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_4, c_2243])).
% 36.20/26.68  tff(c_4174, plain, (![A_331, C_332]: (k2_xboole_0(A_331, k4_xboole_0(A_331, C_332))=A_331)), inference(superposition, [status(thm), theory('equality')], [c_4083, c_2309])).
% 36.20/26.68  tff(c_16, plain, (![A_14, B_15]: (k4_xboole_0(k2_xboole_0(A_14, B_15), k3_xboole_0(A_14, B_15))=k5_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 36.20/26.68  tff(c_16373, plain, (![A_547, B_548]: (k4_xboole_0(k5_xboole_0(A_547, B_548), k2_xboole_0(A_547, B_548))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_4083])).
% 36.20/26.68  tff(c_16560, plain, (![A_331, C_332]: (k4_xboole_0(k5_xboole_0(A_331, k4_xboole_0(A_331, C_332)), A_331)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4174, c_16373])).
% 36.20/26.68  tff(c_43949, plain, (![B_779, A_780]: (k4_xboole_0(B_779, k4_xboole_0(B_779, A_780))=k3_xboole_0(B_779, A_780))), inference(superposition, [status(thm), theory('equality')], [c_43378, c_3953])).
% 36.20/26.68  tff(c_44233, plain, (![B_779, A_780]: (k5_xboole_0(k4_xboole_0(B_779, A_780), k3_xboole_0(B_779, A_780))=k2_xboole_0(k4_xboole_0(B_779, A_780), B_779))), inference(superposition, [status(thm), theory('equality')], [c_43949, c_48])).
% 36.20/26.68  tff(c_83649, plain, (![B_1072, A_1073]: (k5_xboole_0(k4_xboole_0(B_1072, A_1073), k3_xboole_0(B_1072, A_1073))=B_1072)), inference(demodulation, [status(thm), theory('equality')], [c_4174, c_2, c_44233])).
% 36.20/26.68  tff(c_83934, plain, (![A_331, C_332]: (k5_xboole_0(k1_xboole_0, k3_xboole_0(k5_xboole_0(A_331, k4_xboole_0(A_331, C_332)), A_331))=k5_xboole_0(A_331, k4_xboole_0(A_331, C_332)))), inference(superposition, [status(thm), theory('equality')], [c_16560, c_83649])).
% 36.20/26.68  tff(c_84218, plain, (![A_331, C_332]: (k5_xboole_0(A_331, k4_xboole_0(A_331, C_332))=k3_xboole_0(A_331, C_332))), inference(demodulation, [status(thm), theory('equality')], [c_43390, c_42039, c_916, c_4, c_83934])).
% 36.20/26.68  tff(c_136066, plain, (k3_xboole_0('#skF_5', k4_xboole_0('#skF_5', '#skF_6'))=k5_xboole_0('#skF_5', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_135998, c_84218])).
% 36.20/26.68  tff(c_136343, plain, (k4_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3966, c_1599, c_136066])).
% 36.20/26.68  tff(c_136345, plain, $false, inference(negUnitSimplification, [status(thm)], [c_713, c_136343])).
% 36.20/26.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.20/26.68  
% 36.20/26.68  Inference rules
% 36.20/26.68  ----------------------
% 36.20/26.68  #Ref     : 1
% 36.20/26.68  #Sup     : 35292
% 36.20/26.68  #Fact    : 0
% 36.20/26.68  #Define  : 0
% 36.20/26.68  #Split   : 9
% 36.20/26.68  #Chain   : 0
% 36.20/26.68  #Close   : 0
% 36.20/26.68  
% 36.20/26.68  Ordering : KBO
% 36.20/26.68  
% 36.20/26.68  Simplification rules
% 36.20/26.68  ----------------------
% 36.20/26.68  #Subsume      : 4406
% 36.20/26.68  #Demod        : 34453
% 36.20/26.68  #Tautology    : 18088
% 36.20/26.68  #SimpNegUnit  : 744
% 36.20/26.68  #BackRed      : 24
% 36.20/26.68  
% 36.20/26.68  #Partial instantiations: 0
% 36.20/26.68  #Strategies tried      : 1
% 36.20/26.68  
% 36.20/26.68  Timing (in seconds)
% 36.20/26.68  ----------------------
% 36.20/26.69  Preprocessing        : 0.45
% 36.20/26.69  Parsing              : 0.23
% 36.20/26.69  CNF conversion       : 0.04
% 36.20/26.69  Main loop            : 25.43
% 36.20/26.69  Inferencing          : 2.28
% 36.20/26.69  Reduction            : 17.00
% 36.20/26.69  Demodulation         : 15.33
% 36.20/26.69  BG Simplification    : 0.29
% 36.20/26.69  Subsumption          : 4.80
% 36.20/26.69  Abstraction          : 0.55
% 36.20/26.69  MUC search           : 0.00
% 36.20/26.69  Cooper               : 0.00
% 36.20/26.69  Total                : 25.93
% 36.20/26.69  Index Insertion      : 0.00
% 36.20/26.69  Index Deletion       : 0.00
% 36.20/26.69  Index Matching       : 0.00
% 36.20/26.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
