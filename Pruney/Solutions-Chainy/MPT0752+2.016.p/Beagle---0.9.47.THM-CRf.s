%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:28 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 248 expanded)
%              Number of leaves         :   38 (  98 expanded)
%              Depth                    :   17
%              Number of atoms          :  149 ( 432 expanded)
%              Number of equality atoms :   60 ( 120 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > v5_ordinal1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_67,axiom,(
    ! [A,B] :
      ( v4_relat_1(k1_xboole_0,A)
      & v5_relat_1(k1_xboole_0,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t206_relat_1)).

tff(f_126,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(k1_xboole_0)
        & v5_relat_1(k1_xboole_0,A)
        & v1_funct_1(k1_xboole_0)
        & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).

tff(f_117,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v5_relat_1(B,A)
      & v1_funct_1(B)
      & v5_ordinal1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_ordinal1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k8_relat_1(k1_xboole_0,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
        & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k2_relat_1(B))
       => k2_relat_1(k8_relat_1(A,B)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_24,plain,(
    ! [B_15] : v5_relat_1(k1_xboole_0,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_62,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,'#skF_3')
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_73,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_62])).

tff(c_92,plain,(
    ~ v5_ordinal1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_73])).

tff(c_60,plain,(
    ! [A_26] : v1_relat_1('#skF_2'(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_58,plain,(
    ! [A_26] : v5_relat_1('#skF_2'(A_26),A_26) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    ! [A_20] : v1_relat_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_197,plain,(
    ! [A_52] :
      ( k8_relat_1(k1_xboole_0,A_52) = k1_xboole_0
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_217,plain,(
    ! [A_54] : k8_relat_1(k1_xboole_0,k6_relat_1(A_54)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_197])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(k8_relat_1(A_4,B_5))
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_222,plain,(
    ! [A_54] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k6_relat_1(A_54)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_8])).

tff(c_227,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_222])).

tff(c_20,plain,(
    ! [A_13] :
      ( k9_relat_1(A_13,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_247,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_227,c_20])).

tff(c_44,plain,(
    ! [A_20] : v1_funct_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_52,plain,(
    ! [A_21] :
      ( k1_relat_1(k6_relat_1(A_21)) = A_21
      | ~ v1_funct_1(k6_relat_1(A_21))
      | ~ v1_relat_1(k6_relat_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_64,plain,(
    ! [A_21] :
      ( k1_relat_1(k6_relat_1(A_21)) = A_21
      | ~ v1_relat_1(k6_relat_1(A_21)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_52])).

tff(c_68,plain,(
    ! [A_21] : k1_relat_1(k6_relat_1(A_21)) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_64])).

tff(c_289,plain,(
    ! [A_56] :
      ( k7_relat_1(A_56,k1_relat_1(A_56)) = A_56
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_298,plain,(
    ! [A_21] :
      ( k7_relat_1(k6_relat_1(A_21),A_21) = k6_relat_1(A_21)
      | ~ v1_relat_1(k6_relat_1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_289])).

tff(c_315,plain,(
    ! [A_58] : k7_relat_1(k6_relat_1(A_58),A_58) = k6_relat_1(A_58) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_298])).

tff(c_143,plain,(
    ! [A_46] :
      ( k7_relat_1(A_46,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_154,plain,(
    ! [A_20] : k7_relat_1(k6_relat_1(A_20),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_143])).

tff(c_322,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_154])).

tff(c_354,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_68])).

tff(c_497,plain,(
    ! [A_67] :
      ( k9_relat_1(A_67,k1_relat_1(A_67)) = k2_relat_1(A_67)
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_506,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_497])).

tff(c_513,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_247,c_506])).

tff(c_614,plain,(
    ! [B_75,A_76] :
      ( k5_relat_1(B_75,k6_relat_1(A_76)) = k8_relat_1(A_76,B_75)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_177,plain,(
    ! [A_50] :
      ( k5_relat_1(k1_xboole_0,A_50) = k1_xboole_0
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_188,plain,(
    ! [A_20] : k5_relat_1(k1_xboole_0,k6_relat_1(A_20)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_177])).

tff(c_621,plain,(
    ! [A_76] :
      ( k8_relat_1(A_76,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_614,c_188])).

tff(c_633,plain,(
    ! [A_76] : k8_relat_1(A_76,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_621])).

tff(c_818,plain,(
    ! [A_89,B_90] :
      ( k2_relat_1(k8_relat_1(A_89,B_90)) = A_89
      | ~ r1_tarski(A_89,k2_relat_1(B_90))
      | ~ v1_relat_1(B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_832,plain,(
    ! [A_89] :
      ( k2_relat_1(k8_relat_1(A_89,k1_xboole_0)) = A_89
      | ~ r1_tarski(A_89,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_513,c_818])).

tff(c_839,plain,(
    ! [A_91] :
      ( k1_xboole_0 = A_91
      | ~ r1_tarski(A_91,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_513,c_633,c_832])).

tff(c_892,plain,(
    ! [B_93] :
      ( k2_relat_1(B_93) = k1_xboole_0
      | ~ v5_relat_1(B_93,k1_xboole_0)
      | ~ v1_relat_1(B_93) ) ),
    inference(resolution,[status(thm)],[c_4,c_839])).

tff(c_896,plain,
    ( k2_relat_1('#skF_2'(k1_xboole_0)) = k1_xboole_0
    | ~ v1_relat_1('#skF_2'(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_58,c_892])).

tff(c_907,plain,(
    k2_relat_1('#skF_2'(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_896])).

tff(c_249,plain,(
    ! [A_55] :
      ( k2_relat_1(A_55) != k1_xboole_0
      | k1_xboole_0 = A_55
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_266,plain,(
    ! [A_26] :
      ( k2_relat_1('#skF_2'(A_26)) != k1_xboole_0
      | '#skF_2'(A_26) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_60,c_249])).

tff(c_956,plain,(
    '#skF_2'(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_907,c_266])).

tff(c_54,plain,(
    ! [A_26] : v5_ordinal1('#skF_2'(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_981,plain,(
    v5_ordinal1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_956,c_54])).

tff(c_999,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_981])).

tff(c_1000,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_73])).

tff(c_1004,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1000])).

tff(c_1033,plain,(
    ! [A_102] :
      ( k8_relat_1(k1_xboole_0,A_102) = k1_xboole_0
      | ~ v1_relat_1(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1046,plain,(
    ! [A_103] : k8_relat_1(k1_xboole_0,k6_relat_1(A_103)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_1033])).

tff(c_1051,plain,(
    ! [A_103] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k6_relat_1(A_103)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1046,c_8])).

tff(c_1056,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1051])).

tff(c_1058,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1004,c_1056])).

tff(c_1059,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1000])).

tff(c_1249,plain,(
    ! [A_121] :
      ( k1_relat_1(A_121) != k1_xboole_0
      | k1_xboole_0 = A_121
      | ~ v1_relat_1(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1258,plain,(
    ! [A_20] :
      ( k1_relat_1(k6_relat_1(A_20)) != k1_xboole_0
      | k6_relat_1(A_20) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_42,c_1249])).

tff(c_1269,plain,(
    ! [A_122] :
      ( k1_xboole_0 != A_122
      | k6_relat_1(A_122) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1258])).

tff(c_1295,plain,(
    ! [A_122] :
      ( v1_funct_1(k1_xboole_0)
      | k1_xboole_0 != A_122 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1269,c_44])).

tff(c_1308,plain,(
    ! [A_122] : k1_xboole_0 != A_122 ),
    inference(negUnitSimplification,[status(thm)],[c_1059,c_1295])).

tff(c_1185,plain,(
    ! [A_116] :
      ( k8_relat_1(k1_xboole_0,A_116) = k1_xboole_0
      | ~ v1_relat_1(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1201,plain,(
    ! [A_26] : k8_relat_1(k1_xboole_0,'#skF_2'(A_26)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_1185])).

tff(c_1331,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1308,c_1201])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:04:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.54/1.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/1.82  
% 3.60/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/1.82  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > v5_ordinal1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.60/1.82  
% 3.60/1.82  %Foreground sorts:
% 3.60/1.82  
% 3.60/1.82  
% 3.60/1.82  %Background operators:
% 3.60/1.82  
% 3.60/1.82  
% 3.60/1.82  %Foreground operators:
% 3.60/1.82  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.60/1.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.60/1.82  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.60/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.60/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.60/1.82  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.60/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.60/1.82  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.60/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.60/1.82  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.60/1.82  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 3.60/1.82  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.60/1.82  tff('#skF_3', type, '#skF_3': $i).
% 3.60/1.82  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.60/1.82  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.60/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.60/1.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.60/1.82  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.60/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.60/1.82  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.60/1.82  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.60/1.82  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.60/1.82  
% 3.60/1.84  tff(f_67, axiom, (![A, B]: (v4_relat_1(k1_xboole_0, A) & v5_relat_1(k1_xboole_0, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t206_relat_1)).
% 3.60/1.84  tff(f_126, negated_conjecture, ~(![A]: (((v1_relat_1(k1_xboole_0) & v5_relat_1(k1_xboole_0, A)) & v1_funct_1(k1_xboole_0)) & v5_ordinal1(k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_ordinal1)).
% 3.60/1.84  tff(f_117, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) & v5_ordinal1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_ordinal1)).
% 3.60/1.84  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.60/1.84  tff(f_95, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.60/1.84  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (k8_relat_1(k1_xboole_0, A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_relat_1)).
% 3.60/1.84  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 3.60/1.84  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_relat_1)).
% 3.60/1.84  tff(f_108, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 3.60/1.84  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 3.60/1.84  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_relat_1)).
% 3.60/1.84  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 3.60/1.84  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 3.60/1.84  tff(f_73, axiom, (![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 3.60/1.84  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k2_relat_1(B)) => (k2_relat_1(k8_relat_1(A, B)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_relat_1)).
% 3.60/1.84  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.60/1.84  tff(c_24, plain, (![B_15]: (v5_relat_1(k1_xboole_0, B_15))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.60/1.84  tff(c_62, plain, (~v1_relat_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0, '#skF_3') | ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.60/1.84  tff(c_73, plain, (~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_62])).
% 3.60/1.84  tff(c_92, plain, (~v5_ordinal1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_73])).
% 3.60/1.84  tff(c_60, plain, (![A_26]: (v1_relat_1('#skF_2'(A_26)))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.60/1.84  tff(c_58, plain, (![A_26]: (v5_relat_1('#skF_2'(A_26), A_26))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.60/1.84  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.60/1.84  tff(c_42, plain, (![A_20]: (v1_relat_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.60/1.84  tff(c_197, plain, (![A_52]: (k8_relat_1(k1_xboole_0, A_52)=k1_xboole_0 | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.60/1.84  tff(c_217, plain, (![A_54]: (k8_relat_1(k1_xboole_0, k6_relat_1(A_54))=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_197])).
% 3.60/1.84  tff(c_8, plain, (![A_4, B_5]: (v1_relat_1(k8_relat_1(A_4, B_5)) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.60/1.84  tff(c_222, plain, (![A_54]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(k6_relat_1(A_54)))), inference(superposition, [status(thm), theory('equality')], [c_217, c_8])).
% 3.60/1.84  tff(c_227, plain, (v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_222])).
% 3.60/1.84  tff(c_20, plain, (![A_13]: (k9_relat_1(A_13, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.60/1.84  tff(c_247, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_227, c_20])).
% 3.60/1.84  tff(c_44, plain, (![A_20]: (v1_funct_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.60/1.84  tff(c_52, plain, (![A_21]: (k1_relat_1(k6_relat_1(A_21))=A_21 | ~v1_funct_1(k6_relat_1(A_21)) | ~v1_relat_1(k6_relat_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.60/1.84  tff(c_64, plain, (![A_21]: (k1_relat_1(k6_relat_1(A_21))=A_21 | ~v1_relat_1(k6_relat_1(A_21)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_52])).
% 3.60/1.84  tff(c_68, plain, (![A_21]: (k1_relat_1(k6_relat_1(A_21))=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_64])).
% 3.60/1.84  tff(c_289, plain, (![A_56]: (k7_relat_1(A_56, k1_relat_1(A_56))=A_56 | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.60/1.84  tff(c_298, plain, (![A_21]: (k7_relat_1(k6_relat_1(A_21), A_21)=k6_relat_1(A_21) | ~v1_relat_1(k6_relat_1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_289])).
% 3.60/1.84  tff(c_315, plain, (![A_58]: (k7_relat_1(k6_relat_1(A_58), A_58)=k6_relat_1(A_58))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_298])).
% 3.60/1.84  tff(c_143, plain, (![A_46]: (k7_relat_1(A_46, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.60/1.84  tff(c_154, plain, (![A_20]: (k7_relat_1(k6_relat_1(A_20), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_143])).
% 3.60/1.84  tff(c_322, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_315, c_154])).
% 3.60/1.84  tff(c_354, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_322, c_68])).
% 3.60/1.84  tff(c_497, plain, (![A_67]: (k9_relat_1(A_67, k1_relat_1(A_67))=k2_relat_1(A_67) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.60/1.84  tff(c_506, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_354, c_497])).
% 3.60/1.84  tff(c_513, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_227, c_247, c_506])).
% 3.60/1.84  tff(c_614, plain, (![B_75, A_76]: (k5_relat_1(B_75, k6_relat_1(A_76))=k8_relat_1(A_76, B_75) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.60/1.84  tff(c_177, plain, (![A_50]: (k5_relat_1(k1_xboole_0, A_50)=k1_xboole_0 | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.60/1.84  tff(c_188, plain, (![A_20]: (k5_relat_1(k1_xboole_0, k6_relat_1(A_20))=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_177])).
% 3.60/1.84  tff(c_621, plain, (![A_76]: (k8_relat_1(A_76, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_614, c_188])).
% 3.60/1.84  tff(c_633, plain, (![A_76]: (k8_relat_1(A_76, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_227, c_621])).
% 3.60/1.84  tff(c_818, plain, (![A_89, B_90]: (k2_relat_1(k8_relat_1(A_89, B_90))=A_89 | ~r1_tarski(A_89, k2_relat_1(B_90)) | ~v1_relat_1(B_90))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.60/1.84  tff(c_832, plain, (![A_89]: (k2_relat_1(k8_relat_1(A_89, k1_xboole_0))=A_89 | ~r1_tarski(A_89, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_513, c_818])).
% 3.60/1.84  tff(c_839, plain, (![A_91]: (k1_xboole_0=A_91 | ~r1_tarski(A_91, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_227, c_513, c_633, c_832])).
% 3.60/1.84  tff(c_892, plain, (![B_93]: (k2_relat_1(B_93)=k1_xboole_0 | ~v5_relat_1(B_93, k1_xboole_0) | ~v1_relat_1(B_93))), inference(resolution, [status(thm)], [c_4, c_839])).
% 3.60/1.84  tff(c_896, plain, (k2_relat_1('#skF_2'(k1_xboole_0))=k1_xboole_0 | ~v1_relat_1('#skF_2'(k1_xboole_0))), inference(resolution, [status(thm)], [c_58, c_892])).
% 3.60/1.84  tff(c_907, plain, (k2_relat_1('#skF_2'(k1_xboole_0))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_60, c_896])).
% 3.60/1.84  tff(c_249, plain, (![A_55]: (k2_relat_1(A_55)!=k1_xboole_0 | k1_xboole_0=A_55 | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.60/1.84  tff(c_266, plain, (![A_26]: (k2_relat_1('#skF_2'(A_26))!=k1_xboole_0 | '#skF_2'(A_26)=k1_xboole_0)), inference(resolution, [status(thm)], [c_60, c_249])).
% 3.60/1.84  tff(c_956, plain, ('#skF_2'(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_907, c_266])).
% 3.60/1.84  tff(c_54, plain, (![A_26]: (v5_ordinal1('#skF_2'(A_26)))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.60/1.84  tff(c_981, plain, (v5_ordinal1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_956, c_54])).
% 3.60/1.84  tff(c_999, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_981])).
% 3.60/1.84  tff(c_1000, plain, (~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_73])).
% 3.60/1.84  tff(c_1004, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1000])).
% 3.60/1.84  tff(c_1033, plain, (![A_102]: (k8_relat_1(k1_xboole_0, A_102)=k1_xboole_0 | ~v1_relat_1(A_102))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.60/1.84  tff(c_1046, plain, (![A_103]: (k8_relat_1(k1_xboole_0, k6_relat_1(A_103))=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_1033])).
% 3.60/1.84  tff(c_1051, plain, (![A_103]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(k6_relat_1(A_103)))), inference(superposition, [status(thm), theory('equality')], [c_1046, c_8])).
% 3.60/1.84  tff(c_1056, plain, (v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1051])).
% 3.60/1.84  tff(c_1058, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1004, c_1056])).
% 3.60/1.84  tff(c_1059, plain, (~v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_1000])).
% 3.60/1.84  tff(c_1249, plain, (![A_121]: (k1_relat_1(A_121)!=k1_xboole_0 | k1_xboole_0=A_121 | ~v1_relat_1(A_121))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.60/1.84  tff(c_1258, plain, (![A_20]: (k1_relat_1(k6_relat_1(A_20))!=k1_xboole_0 | k6_relat_1(A_20)=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_1249])).
% 3.60/1.84  tff(c_1269, plain, (![A_122]: (k1_xboole_0!=A_122 | k6_relat_1(A_122)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1258])).
% 3.60/1.84  tff(c_1295, plain, (![A_122]: (v1_funct_1(k1_xboole_0) | k1_xboole_0!=A_122)), inference(superposition, [status(thm), theory('equality')], [c_1269, c_44])).
% 3.60/1.84  tff(c_1308, plain, (![A_122]: (k1_xboole_0!=A_122)), inference(negUnitSimplification, [status(thm)], [c_1059, c_1295])).
% 3.60/1.84  tff(c_1185, plain, (![A_116]: (k8_relat_1(k1_xboole_0, A_116)=k1_xboole_0 | ~v1_relat_1(A_116))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.60/1.84  tff(c_1201, plain, (![A_26]: (k8_relat_1(k1_xboole_0, '#skF_2'(A_26))=k1_xboole_0)), inference(resolution, [status(thm)], [c_60, c_1185])).
% 3.60/1.84  tff(c_1331, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1308, c_1201])).
% 3.60/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/1.84  
% 3.60/1.84  Inference rules
% 3.60/1.84  ----------------------
% 3.60/1.84  #Ref     : 0
% 3.60/1.84  #Sup     : 297
% 3.60/1.84  #Fact    : 0
% 3.60/1.84  #Define  : 0
% 3.60/1.84  #Split   : 2
% 3.60/1.84  #Chain   : 0
% 3.60/1.84  #Close   : 0
% 3.60/1.84  
% 3.60/1.84  Ordering : KBO
% 3.60/1.84  
% 3.60/1.84  Simplification rules
% 3.60/1.84  ----------------------
% 3.60/1.84  #Subsume      : 4
% 3.60/1.84  #Demod        : 192
% 3.60/1.84  #Tautology    : 212
% 3.60/1.84  #SimpNegUnit  : 24
% 3.60/1.84  #BackRed      : 20
% 3.60/1.84  
% 3.60/1.84  #Partial instantiations: 0
% 3.60/1.84  #Strategies tried      : 1
% 3.60/1.84  
% 3.60/1.84  Timing (in seconds)
% 3.60/1.84  ----------------------
% 3.60/1.84  Preprocessing        : 0.50
% 3.60/1.84  Parsing              : 0.28
% 3.60/1.84  CNF conversion       : 0.03
% 3.60/1.84  Main loop            : 0.51
% 3.60/1.84  Inferencing          : 0.19
% 3.60/1.84  Reduction            : 0.17
% 3.60/1.84  Demodulation         : 0.12
% 3.60/1.84  BG Simplification    : 0.03
% 3.60/1.84  Subsumption          : 0.07
% 3.60/1.84  Abstraction          : 0.02
% 3.60/1.84  MUC search           : 0.00
% 3.60/1.84  Cooper               : 0.00
% 3.60/1.84  Total                : 1.05
% 3.60/1.84  Index Insertion      : 0.00
% 3.60/1.84  Index Deletion       : 0.00
% 3.60/1.84  Index Matching       : 0.00
% 3.60/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
