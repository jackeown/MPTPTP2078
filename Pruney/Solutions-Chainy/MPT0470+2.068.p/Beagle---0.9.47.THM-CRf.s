%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:10 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 199 expanded)
%              Number of leaves         :   37 (  82 expanded)
%              Depth                    :   16
%              Number of atoms          :  159 ( 326 expanded)
%              Number of equality atoms :   52 ( 117 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_relat_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k4_relat_1 > k3_tarski > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_100,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_28,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k6_subset_1(A,B)) = k6_subset_1(k4_relat_1(A),k4_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_relat_1)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(c_44,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_77,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_46,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_63,plain,(
    ! [A_42] :
      ( v1_relat_1(A_42)
      | ~ v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_67,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_63])).

tff(c_28,plain,(
    ! [A_27,B_28] :
      ( v1_relat_1(k5_relat_1(A_27,B_28))
      | ~ v1_relat_1(B_28)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_42,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_40,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_220,plain,(
    ! [A_74,B_75] :
      ( k1_relat_1(k5_relat_1(A_74,B_75)) = k1_relat_1(A_74)
      | ~ r1_tarski(k2_relat_1(A_74),k1_relat_1(B_75))
      | ~ v1_relat_1(B_75)
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_226,plain,(
    ! [B_75] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_75)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_75))
      | ~ v1_relat_1(B_75)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_220])).

tff(c_231,plain,(
    ! [B_76] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_76)) = k1_xboole_0
      | ~ v1_relat_1(B_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_8,c_42,c_226])).

tff(c_30,plain,(
    ! [A_29] :
      ( ~ v1_xboole_0(k1_relat_1(A_29))
      | ~ v1_relat_1(A_29)
      | v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_240,plain,(
    ! [B_76] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_76))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_76))
      | ~ v1_relat_1(B_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_30])).

tff(c_304,plain,(
    ! [B_80] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_80))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_80))
      | ~ v1_relat_1(B_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_240])).

tff(c_6,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_330,plain,(
    ! [B_82] :
      ( k5_relat_1(k1_xboole_0,B_82) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_82))
      | ~ v1_relat_1(B_82) ) ),
    inference(resolution,[status(thm)],[c_304,c_6])).

tff(c_334,plain,(
    ! [B_28] :
      ( k5_relat_1(k1_xboole_0,B_28) = k1_xboole_0
      | ~ v1_relat_1(B_28)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_28,c_330])).

tff(c_368,plain,(
    ! [B_84] :
      ( k5_relat_1(k1_xboole_0,B_84) = k1_xboole_0
      | ~ v1_relat_1(B_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_334])).

tff(c_383,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_368])).

tff(c_391,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_383])).

tff(c_392,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_4,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_399,plain,(
    ! [A_86,B_87] : k4_xboole_0(A_86,k2_xboole_0(A_86,B_87)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_406,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_399])).

tff(c_22,plain,(
    ! [A_23,B_24] : k6_subset_1(A_23,B_24) = k4_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_34,plain,(
    ! [A_31,B_33] :
      ( k6_subset_1(k4_relat_1(A_31),k4_relat_1(B_33)) = k4_relat_1(k6_subset_1(A_31,B_33))
      | ~ v1_relat_1(B_33)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_502,plain,(
    ! [A_111,B_112] :
      ( k4_xboole_0(k4_relat_1(A_111),k4_relat_1(B_112)) = k4_relat_1(k4_xboole_0(A_111,B_112))
      | ~ v1_relat_1(B_112)
      | ~ v1_relat_1(A_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_34])).

tff(c_509,plain,(
    ! [B_112] :
      ( k4_relat_1(k4_xboole_0(B_112,B_112)) = k1_xboole_0
      | ~ v1_relat_1(B_112)
      | ~ v1_relat_1(B_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_502,c_406])).

tff(c_524,plain,(
    ! [B_112] :
      ( k4_relat_1(k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_112)
      | ~ v1_relat_1(B_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_509])).

tff(c_528,plain,(
    ! [B_113] :
      ( ~ v1_relat_1(B_113)
      | ~ v1_relat_1(B_113) ) ),
    inference(splitLeft,[status(thm)],[c_524])).

tff(c_534,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_67,c_528])).

tff(c_542,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_534])).

tff(c_543,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_524])).

tff(c_38,plain,(
    ! [B_39,A_37] :
      ( k5_relat_1(k4_relat_1(B_39),k4_relat_1(A_37)) = k4_relat_1(k5_relat_1(A_37,B_39))
      | ~ v1_relat_1(B_39)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_565,plain,(
    ! [A_37] :
      ( k5_relat_1(k1_xboole_0,k4_relat_1(A_37)) = k4_relat_1(k5_relat_1(A_37,k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_543,c_38])).

tff(c_910,plain,(
    ! [A_129] :
      ( k5_relat_1(k1_xboole_0,k4_relat_1(A_129)) = k4_relat_1(k5_relat_1(A_129,k1_xboole_0))
      | ~ v1_relat_1(A_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_565])).

tff(c_26,plain,(
    ! [A_26] :
      ( v1_relat_1(k4_relat_1(A_26))
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_614,plain,(
    ! [A_117,B_118] :
      ( k1_relat_1(k5_relat_1(A_117,B_118)) = k1_relat_1(A_117)
      | ~ r1_tarski(k2_relat_1(A_117),k1_relat_1(B_118))
      | ~ v1_relat_1(B_118)
      | ~ v1_relat_1(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_620,plain,(
    ! [B_118] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_118)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_118))
      | ~ v1_relat_1(B_118)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_614])).

tff(c_625,plain,(
    ! [B_119] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_119)) = k1_xboole_0
      | ~ v1_relat_1(B_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_8,c_42,c_620])).

tff(c_634,plain,(
    ! [B_119] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_119))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_119))
      | ~ v1_relat_1(B_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_625,c_30])).

tff(c_647,plain,(
    ! [B_120] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_120))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_120))
      | ~ v1_relat_1(B_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_634])).

tff(c_772,plain,(
    ! [B_124] :
      ( k5_relat_1(k1_xboole_0,B_124) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_124))
      | ~ v1_relat_1(B_124) ) ),
    inference(resolution,[status(thm)],[c_647,c_6])).

tff(c_776,plain,(
    ! [B_28] :
      ( k5_relat_1(k1_xboole_0,B_28) = k1_xboole_0
      | ~ v1_relat_1(B_28)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_28,c_772])).

tff(c_852,plain,(
    ! [B_127] :
      ( k5_relat_1(k1_xboole_0,B_127) = k1_xboole_0
      | ~ v1_relat_1(B_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_776])).

tff(c_870,plain,(
    ! [A_26] :
      ( k5_relat_1(k1_xboole_0,k4_relat_1(A_26)) = k1_xboole_0
      | ~ v1_relat_1(A_26) ) ),
    inference(resolution,[status(thm)],[c_26,c_852])).

tff(c_1014,plain,(
    ! [A_132] :
      ( k4_relat_1(k5_relat_1(A_132,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_132)
      | ~ v1_relat_1(A_132) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_910,c_870])).

tff(c_32,plain,(
    ! [A_30] :
      ( k4_relat_1(k4_relat_1(A_30)) = A_30
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1050,plain,(
    ! [A_132] :
      ( k5_relat_1(A_132,k1_xboole_0) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_132,k1_xboole_0))
      | ~ v1_relat_1(A_132)
      | ~ v1_relat_1(A_132) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1014,c_32])).

tff(c_1519,plain,(
    ! [A_141] :
      ( k5_relat_1(A_141,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_141,k1_xboole_0))
      | ~ v1_relat_1(A_141)
      | ~ v1_relat_1(A_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_543,c_1050])).

tff(c_1529,plain,(
    ! [A_27] :
      ( k5_relat_1(A_27,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_27) ) ),
    inference(resolution,[status(thm)],[c_28,c_1519])).

tff(c_1535,plain,(
    ! [A_142] :
      ( k5_relat_1(A_142,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_1529])).

tff(c_1556,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_1535])).

tff(c_1567,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_392,c_1556])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:10:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.37/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/1.72  
% 3.73/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/1.72  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_relat_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k4_relat_1 > k3_tarski > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 3.73/1.72  
% 3.73/1.72  %Foreground sorts:
% 3.73/1.72  
% 3.73/1.72  
% 3.73/1.72  %Background operators:
% 3.73/1.72  
% 3.73/1.72  
% 3.73/1.72  %Foreground operators:
% 3.73/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.73/1.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.73/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.73/1.72  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.73/1.72  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.73/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.73/1.72  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.73/1.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.73/1.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.73/1.72  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.73/1.72  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.73/1.72  tff('#skF_1', type, '#skF_1': $i).
% 3.73/1.72  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.73/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.73/1.72  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.73/1.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.73/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.73/1.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.73/1.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.73/1.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.73/1.72  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.73/1.72  
% 3.73/1.74  tff(f_107, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 3.73/1.74  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.73/1.74  tff(f_52, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.73/1.74  tff(f_62, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.73/1.74  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.73/1.74  tff(f_100, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.73/1.74  tff(f_90, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 3.73/1.74  tff(f_70, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_relat_1)).
% 3.73/1.74  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.73/1.74  tff(f_28, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.73/1.74  tff(f_36, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.73/1.74  tff(f_48, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.73/1.74  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k6_subset_1(A, B)) = k6_subset_1(k4_relat_1(A), k4_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_relat_1)).
% 3.73/1.74  tff(f_97, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 3.73/1.74  tff(f_56, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 3.73/1.74  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 3.73/1.74  tff(c_44, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.73/1.74  tff(c_77, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_44])).
% 3.73/1.74  tff(c_46, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.73/1.74  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.73/1.74  tff(c_63, plain, (![A_42]: (v1_relat_1(A_42) | ~v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.73/1.74  tff(c_67, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_63])).
% 3.73/1.74  tff(c_28, plain, (![A_27, B_28]: (v1_relat_1(k5_relat_1(A_27, B_28)) | ~v1_relat_1(B_28) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.73/1.74  tff(c_8, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.73/1.74  tff(c_42, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.73/1.74  tff(c_40, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.73/1.74  tff(c_220, plain, (![A_74, B_75]: (k1_relat_1(k5_relat_1(A_74, B_75))=k1_relat_1(A_74) | ~r1_tarski(k2_relat_1(A_74), k1_relat_1(B_75)) | ~v1_relat_1(B_75) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.73/1.74  tff(c_226, plain, (![B_75]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_75))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_75)) | ~v1_relat_1(B_75) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40, c_220])).
% 3.73/1.74  tff(c_231, plain, (![B_76]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_76))=k1_xboole_0 | ~v1_relat_1(B_76))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_8, c_42, c_226])).
% 3.73/1.74  tff(c_30, plain, (![A_29]: (~v1_xboole_0(k1_relat_1(A_29)) | ~v1_relat_1(A_29) | v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.73/1.74  tff(c_240, plain, (![B_76]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_76)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_76)) | ~v1_relat_1(B_76))), inference(superposition, [status(thm), theory('equality')], [c_231, c_30])).
% 3.73/1.74  tff(c_304, plain, (![B_80]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_80)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_80)) | ~v1_relat_1(B_80))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_240])).
% 3.73/1.74  tff(c_6, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.73/1.74  tff(c_330, plain, (![B_82]: (k5_relat_1(k1_xboole_0, B_82)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_82)) | ~v1_relat_1(B_82))), inference(resolution, [status(thm)], [c_304, c_6])).
% 3.73/1.74  tff(c_334, plain, (![B_28]: (k5_relat_1(k1_xboole_0, B_28)=k1_xboole_0 | ~v1_relat_1(B_28) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_330])).
% 3.73/1.74  tff(c_368, plain, (![B_84]: (k5_relat_1(k1_xboole_0, B_84)=k1_xboole_0 | ~v1_relat_1(B_84))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_334])).
% 3.73/1.74  tff(c_383, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_368])).
% 3.73/1.74  tff(c_391, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_383])).
% 3.73/1.74  tff(c_392, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_44])).
% 3.73/1.74  tff(c_4, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.73/1.74  tff(c_399, plain, (![A_86, B_87]: (k4_xboole_0(A_86, k2_xboole_0(A_86, B_87))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.73/1.74  tff(c_406, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_399])).
% 3.73/1.74  tff(c_22, plain, (![A_23, B_24]: (k6_subset_1(A_23, B_24)=k4_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.73/1.74  tff(c_34, plain, (![A_31, B_33]: (k6_subset_1(k4_relat_1(A_31), k4_relat_1(B_33))=k4_relat_1(k6_subset_1(A_31, B_33)) | ~v1_relat_1(B_33) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.73/1.74  tff(c_502, plain, (![A_111, B_112]: (k4_xboole_0(k4_relat_1(A_111), k4_relat_1(B_112))=k4_relat_1(k4_xboole_0(A_111, B_112)) | ~v1_relat_1(B_112) | ~v1_relat_1(A_111))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_34])).
% 3.73/1.74  tff(c_509, plain, (![B_112]: (k4_relat_1(k4_xboole_0(B_112, B_112))=k1_xboole_0 | ~v1_relat_1(B_112) | ~v1_relat_1(B_112))), inference(superposition, [status(thm), theory('equality')], [c_502, c_406])).
% 3.73/1.74  tff(c_524, plain, (![B_112]: (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_112) | ~v1_relat_1(B_112))), inference(demodulation, [status(thm), theory('equality')], [c_406, c_509])).
% 3.73/1.74  tff(c_528, plain, (![B_113]: (~v1_relat_1(B_113) | ~v1_relat_1(B_113))), inference(splitLeft, [status(thm)], [c_524])).
% 3.73/1.74  tff(c_534, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_67, c_528])).
% 3.73/1.74  tff(c_542, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_534])).
% 3.73/1.74  tff(c_543, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_524])).
% 3.73/1.74  tff(c_38, plain, (![B_39, A_37]: (k5_relat_1(k4_relat_1(B_39), k4_relat_1(A_37))=k4_relat_1(k5_relat_1(A_37, B_39)) | ~v1_relat_1(B_39) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.73/1.74  tff(c_565, plain, (![A_37]: (k5_relat_1(k1_xboole_0, k4_relat_1(A_37))=k4_relat_1(k5_relat_1(A_37, k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_37))), inference(superposition, [status(thm), theory('equality')], [c_543, c_38])).
% 3.73/1.74  tff(c_910, plain, (![A_129]: (k5_relat_1(k1_xboole_0, k4_relat_1(A_129))=k4_relat_1(k5_relat_1(A_129, k1_xboole_0)) | ~v1_relat_1(A_129))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_565])).
% 3.73/1.74  tff(c_26, plain, (![A_26]: (v1_relat_1(k4_relat_1(A_26)) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.73/1.74  tff(c_614, plain, (![A_117, B_118]: (k1_relat_1(k5_relat_1(A_117, B_118))=k1_relat_1(A_117) | ~r1_tarski(k2_relat_1(A_117), k1_relat_1(B_118)) | ~v1_relat_1(B_118) | ~v1_relat_1(A_117))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.73/1.74  tff(c_620, plain, (![B_118]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_118))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_118)) | ~v1_relat_1(B_118) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40, c_614])).
% 3.73/1.74  tff(c_625, plain, (![B_119]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_119))=k1_xboole_0 | ~v1_relat_1(B_119))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_8, c_42, c_620])).
% 3.73/1.74  tff(c_634, plain, (![B_119]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_119)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_119)) | ~v1_relat_1(B_119))), inference(superposition, [status(thm), theory('equality')], [c_625, c_30])).
% 3.73/1.74  tff(c_647, plain, (![B_120]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_120)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_120)) | ~v1_relat_1(B_120))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_634])).
% 3.73/1.74  tff(c_772, plain, (![B_124]: (k5_relat_1(k1_xboole_0, B_124)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_124)) | ~v1_relat_1(B_124))), inference(resolution, [status(thm)], [c_647, c_6])).
% 3.73/1.74  tff(c_776, plain, (![B_28]: (k5_relat_1(k1_xboole_0, B_28)=k1_xboole_0 | ~v1_relat_1(B_28) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_772])).
% 3.73/1.74  tff(c_852, plain, (![B_127]: (k5_relat_1(k1_xboole_0, B_127)=k1_xboole_0 | ~v1_relat_1(B_127))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_776])).
% 3.73/1.74  tff(c_870, plain, (![A_26]: (k5_relat_1(k1_xboole_0, k4_relat_1(A_26))=k1_xboole_0 | ~v1_relat_1(A_26))), inference(resolution, [status(thm)], [c_26, c_852])).
% 3.73/1.74  tff(c_1014, plain, (![A_132]: (k4_relat_1(k5_relat_1(A_132, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_132) | ~v1_relat_1(A_132))), inference(superposition, [status(thm), theory('equality')], [c_910, c_870])).
% 3.73/1.74  tff(c_32, plain, (![A_30]: (k4_relat_1(k4_relat_1(A_30))=A_30 | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.73/1.74  tff(c_1050, plain, (![A_132]: (k5_relat_1(A_132, k1_xboole_0)=k4_relat_1(k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_132, k1_xboole_0)) | ~v1_relat_1(A_132) | ~v1_relat_1(A_132))), inference(superposition, [status(thm), theory('equality')], [c_1014, c_32])).
% 3.73/1.74  tff(c_1519, plain, (![A_141]: (k5_relat_1(A_141, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_141, k1_xboole_0)) | ~v1_relat_1(A_141) | ~v1_relat_1(A_141))), inference(demodulation, [status(thm), theory('equality')], [c_543, c_1050])).
% 3.73/1.74  tff(c_1529, plain, (![A_27]: (k5_relat_1(A_27, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_27))), inference(resolution, [status(thm)], [c_28, c_1519])).
% 3.73/1.74  tff(c_1535, plain, (![A_142]: (k5_relat_1(A_142, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_142))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_1529])).
% 3.73/1.74  tff(c_1556, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_1535])).
% 3.73/1.74  tff(c_1567, plain, $false, inference(negUnitSimplification, [status(thm)], [c_392, c_1556])).
% 3.73/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/1.74  
% 3.73/1.74  Inference rules
% 3.73/1.74  ----------------------
% 3.73/1.74  #Ref     : 0
% 3.73/1.74  #Sup     : 360
% 3.73/1.74  #Fact    : 0
% 3.73/1.74  #Define  : 0
% 3.73/1.74  #Split   : 4
% 3.73/1.74  #Chain   : 0
% 3.73/1.74  #Close   : 0
% 3.73/1.74  
% 3.73/1.74  Ordering : KBO
% 3.73/1.74  
% 3.73/1.74  Simplification rules
% 3.73/1.74  ----------------------
% 3.73/1.74  #Subsume      : 19
% 3.73/1.74  #Demod        : 318
% 3.73/1.74  #Tautology    : 199
% 3.73/1.74  #SimpNegUnit  : 2
% 3.73/1.74  #BackRed      : 4
% 3.73/1.74  
% 3.73/1.74  #Partial instantiations: 0
% 3.73/1.74  #Strategies tried      : 1
% 3.73/1.74  
% 3.73/1.74  Timing (in seconds)
% 3.73/1.74  ----------------------
% 3.73/1.74  Preprocessing        : 0.35
% 3.73/1.74  Parsing              : 0.19
% 3.73/1.74  CNF conversion       : 0.02
% 3.73/1.74  Main loop            : 0.51
% 3.73/1.74  Inferencing          : 0.19
% 3.73/1.74  Reduction            : 0.15
% 3.73/1.74  Demodulation         : 0.11
% 3.73/1.74  BG Simplification    : 0.03
% 3.73/1.74  Subsumption          : 0.10
% 3.73/1.74  Abstraction          : 0.03
% 3.73/1.74  MUC search           : 0.00
% 3.73/1.74  Cooper               : 0.00
% 3.73/1.74  Total                : 0.90
% 3.73/1.74  Index Insertion      : 0.00
% 3.73/1.74  Index Deletion       : 0.00
% 3.73/1.74  Index Matching       : 0.00
% 3.73/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
