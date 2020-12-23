%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:10 EST 2020

% Result     : Theorem 3.41s
% Output     : CNFRefutation 3.41s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 215 expanded)
%              Number of leaves         :   36 (  86 expanded)
%              Depth                    :   16
%              Number of atoms          :  162 ( 344 expanded)
%              Number of equality atoms :   55 ( 135 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_98,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_32,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_36,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_38,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k6_subset_1(A,B)) = k6_subset_1(k4_relat_1(A),k4_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_relat_1)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(c_42,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_75,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_44,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_64,plain,(
    ! [A_33] :
      ( v1_relat_1(A_33)
      | ~ v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_68,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_64])).

tff(c_26,plain,(
    ! [A_18,B_19] :
      ( v1_relat_1(k5_relat_1(A_18,B_19))
      | ~ v1_relat_1(B_19)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_40,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_38,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_421,plain,(
    ! [A_64,B_65] :
      ( k1_relat_1(k5_relat_1(A_64,B_65)) = k1_relat_1(A_64)
      | ~ r1_tarski(k2_relat_1(A_64),k1_relat_1(B_65))
      | ~ v1_relat_1(B_65)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_427,plain,(
    ! [B_65] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_65)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_65))
      | ~ v1_relat_1(B_65)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_421])).

tff(c_432,plain,(
    ! [B_66] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_66)) = k1_xboole_0
      | ~ v1_relat_1(B_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_8,c_40,c_427])).

tff(c_28,plain,(
    ! [A_20] :
      ( ~ v1_xboole_0(k1_relat_1(A_20))
      | ~ v1_relat_1(A_20)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_441,plain,(
    ! [B_66] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_66))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_66))
      | ~ v1_relat_1(B_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_28])).

tff(c_452,plain,(
    ! [B_67] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_67))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_67))
      | ~ v1_relat_1(B_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_441])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_464,plain,(
    ! [B_68] :
      ( k5_relat_1(k1_xboole_0,B_68) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_68))
      | ~ v1_relat_1(B_68) ) ),
    inference(resolution,[status(thm)],[c_452,c_4])).

tff(c_471,plain,(
    ! [B_19] :
      ( k5_relat_1(k1_xboole_0,B_19) = k1_xboole_0
      | ~ v1_relat_1(B_19)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26,c_464])).

tff(c_524,plain,(
    ! [B_71] :
      ( k5_relat_1(k1_xboole_0,B_71) = k1_xboole_0
      | ~ v1_relat_1(B_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_471])).

tff(c_536,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_524])).

tff(c_543,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_536])).

tff(c_544,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_6,plain,(
    ! [A_2] : k3_xboole_0(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_617,plain,(
    ! [A_84,B_85] : k4_xboole_0(A_84,k4_xboole_0(A_84,B_85)) = k3_xboole_0(A_84,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_632,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k3_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_617])).

tff(c_635,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_632])).

tff(c_18,plain,(
    ! [A_12,B_13] : k6_subset_1(A_12,B_13) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_32,plain,(
    ! [A_22,B_24] :
      ( k6_subset_1(k4_relat_1(A_22),k4_relat_1(B_24)) = k4_relat_1(k6_subset_1(A_22,B_24))
      | ~ v1_relat_1(B_24)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_862,plain,(
    ! [A_103,B_104] :
      ( k4_xboole_0(k4_relat_1(A_103),k4_relat_1(B_104)) = k4_relat_1(k4_xboole_0(A_103,B_104))
      | ~ v1_relat_1(B_104)
      | ~ v1_relat_1(A_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_32])).

tff(c_872,plain,(
    ! [B_104] :
      ( k4_relat_1(k4_xboole_0(B_104,B_104)) = k1_xboole_0
      | ~ v1_relat_1(B_104)
      | ~ v1_relat_1(B_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_862,c_635])).

tff(c_891,plain,(
    ! [B_104] :
      ( k4_relat_1(k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_104)
      | ~ v1_relat_1(B_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_635,c_872])).

tff(c_895,plain,(
    ! [B_105] :
      ( ~ v1_relat_1(B_105)
      | ~ v1_relat_1(B_105) ) ),
    inference(splitLeft,[status(thm)],[c_891])).

tff(c_901,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_68,c_895])).

tff(c_909,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_901])).

tff(c_910,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_891])).

tff(c_36,plain,(
    ! [B_30,A_28] :
      ( k5_relat_1(k4_relat_1(B_30),k4_relat_1(A_28)) = k4_relat_1(k5_relat_1(A_28,B_30))
      | ~ v1_relat_1(B_30)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_920,plain,(
    ! [A_28] :
      ( k5_relat_1(k1_xboole_0,k4_relat_1(A_28)) = k4_relat_1(k5_relat_1(A_28,k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_910,c_36])).

tff(c_998,plain,(
    ! [A_108] :
      ( k5_relat_1(k1_xboole_0,k4_relat_1(A_108)) = k4_relat_1(k5_relat_1(A_108,k1_xboole_0))
      | ~ v1_relat_1(A_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_920])).

tff(c_24,plain,(
    ! [A_17] :
      ( v1_relat_1(k4_relat_1(A_17))
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_765,plain,(
    ! [A_97,B_98] :
      ( k1_relat_1(k5_relat_1(A_97,B_98)) = k1_relat_1(A_97)
      | ~ r1_tarski(k2_relat_1(A_97),k1_relat_1(B_98))
      | ~ v1_relat_1(B_98)
      | ~ v1_relat_1(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_771,plain,(
    ! [B_98] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_98)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_98))
      | ~ v1_relat_1(B_98)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_765])).

tff(c_776,plain,(
    ! [B_99] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_99)) = k1_xboole_0
      | ~ v1_relat_1(B_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_8,c_40,c_771])).

tff(c_785,plain,(
    ! [B_99] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_99))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_99))
      | ~ v1_relat_1(B_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_776,c_28])).

tff(c_798,plain,(
    ! [B_100] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_100))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_100))
      | ~ v1_relat_1(B_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_785])).

tff(c_812,plain,(
    ! [B_101] :
      ( k5_relat_1(k1_xboole_0,B_101) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_101))
      | ~ v1_relat_1(B_101) ) ),
    inference(resolution,[status(thm)],[c_798,c_4])).

tff(c_816,plain,(
    ! [B_19] :
      ( k5_relat_1(k1_xboole_0,B_19) = k1_xboole_0
      | ~ v1_relat_1(B_19)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26,c_812])).

tff(c_825,plain,(
    ! [B_102] :
      ( k5_relat_1(k1_xboole_0,B_102) = k1_xboole_0
      | ~ v1_relat_1(B_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_816])).

tff(c_839,plain,(
    ! [A_17] :
      ( k5_relat_1(k1_xboole_0,k4_relat_1(A_17)) = k1_xboole_0
      | ~ v1_relat_1(A_17) ) ),
    inference(resolution,[status(thm)],[c_24,c_825])).

tff(c_1032,plain,(
    ! [A_109] :
      ( k4_relat_1(k5_relat_1(A_109,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_109)
      | ~ v1_relat_1(A_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_998,c_839])).

tff(c_30,plain,(
    ! [A_21] :
      ( k4_relat_1(k4_relat_1(A_21)) = A_21
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1059,plain,(
    ! [A_109] :
      ( k5_relat_1(A_109,k1_xboole_0) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_109,k1_xboole_0))
      | ~ v1_relat_1(A_109)
      | ~ v1_relat_1(A_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1032,c_30])).

tff(c_1520,plain,(
    ! [A_122] :
      ( k5_relat_1(A_122,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_122,k1_xboole_0))
      | ~ v1_relat_1(A_122)
      | ~ v1_relat_1(A_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_910,c_1059])).

tff(c_1530,plain,(
    ! [A_18] :
      ( k5_relat_1(A_18,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_18) ) ),
    inference(resolution,[status(thm)],[c_26,c_1520])).

tff(c_1536,plain,(
    ! [A_123] :
      ( k5_relat_1(A_123,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1530])).

tff(c_1557,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_1536])).

tff(c_1568,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_544,c_1557])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:00:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.41/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.41/1.63  
% 3.41/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.41/1.63  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 3.41/1.63  
% 3.41/1.63  %Foreground sorts:
% 3.41/1.63  
% 3.41/1.63  
% 3.41/1.63  %Background operators:
% 3.41/1.63  
% 3.41/1.63  
% 3.41/1.63  %Foreground operators:
% 3.41/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.41/1.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.41/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.41/1.63  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.41/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.41/1.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.41/1.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.41/1.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.41/1.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.41/1.63  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.41/1.63  tff('#skF_1', type, '#skF_1': $i).
% 3.41/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.41/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.41/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.41/1.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.41/1.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.41/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.41/1.63  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.41/1.63  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.41/1.63  
% 3.41/1.64  tff(f_105, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 3.41/1.64  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.41/1.64  tff(f_50, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.41/1.64  tff(f_60, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.41/1.64  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.41/1.64  tff(f_98, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.41/1.64  tff(f_88, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 3.41/1.64  tff(f_68, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_relat_1)).
% 3.41/1.64  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.41/1.64  tff(f_32, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.41/1.64  tff(f_36, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.41/1.64  tff(f_38, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.41/1.64  tff(f_44, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.41/1.64  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k6_subset_1(A, B)) = k6_subset_1(k4_relat_1(A), k4_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_relat_1)).
% 3.41/1.64  tff(f_95, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 3.41/1.64  tff(f_54, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 3.41/1.64  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 3.41/1.64  tff(c_42, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.41/1.64  tff(c_75, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_42])).
% 3.41/1.64  tff(c_44, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.41/1.64  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.41/1.64  tff(c_64, plain, (![A_33]: (v1_relat_1(A_33) | ~v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.41/1.64  tff(c_68, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_64])).
% 3.41/1.64  tff(c_26, plain, (![A_18, B_19]: (v1_relat_1(k5_relat_1(A_18, B_19)) | ~v1_relat_1(B_19) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.41/1.64  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.41/1.64  tff(c_40, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.41/1.64  tff(c_38, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.41/1.64  tff(c_421, plain, (![A_64, B_65]: (k1_relat_1(k5_relat_1(A_64, B_65))=k1_relat_1(A_64) | ~r1_tarski(k2_relat_1(A_64), k1_relat_1(B_65)) | ~v1_relat_1(B_65) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.41/1.64  tff(c_427, plain, (![B_65]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_65))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_65)) | ~v1_relat_1(B_65) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_38, c_421])).
% 3.41/1.64  tff(c_432, plain, (![B_66]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_66))=k1_xboole_0 | ~v1_relat_1(B_66))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_8, c_40, c_427])).
% 3.41/1.64  tff(c_28, plain, (![A_20]: (~v1_xboole_0(k1_relat_1(A_20)) | ~v1_relat_1(A_20) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.41/1.64  tff(c_441, plain, (![B_66]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_66)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_66)) | ~v1_relat_1(B_66))), inference(superposition, [status(thm), theory('equality')], [c_432, c_28])).
% 3.41/1.64  tff(c_452, plain, (![B_67]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_67)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_67)) | ~v1_relat_1(B_67))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_441])).
% 3.41/1.64  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.41/1.64  tff(c_464, plain, (![B_68]: (k5_relat_1(k1_xboole_0, B_68)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_68)) | ~v1_relat_1(B_68))), inference(resolution, [status(thm)], [c_452, c_4])).
% 3.41/1.64  tff(c_471, plain, (![B_19]: (k5_relat_1(k1_xboole_0, B_19)=k1_xboole_0 | ~v1_relat_1(B_19) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_464])).
% 3.41/1.64  tff(c_524, plain, (![B_71]: (k5_relat_1(k1_xboole_0, B_71)=k1_xboole_0 | ~v1_relat_1(B_71))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_471])).
% 3.41/1.64  tff(c_536, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_524])).
% 3.41/1.64  tff(c_543, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_536])).
% 3.41/1.64  tff(c_544, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 3.41/1.64  tff(c_6, plain, (![A_2]: (k3_xboole_0(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.41/1.64  tff(c_10, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.41/1.64  tff(c_617, plain, (![A_84, B_85]: (k4_xboole_0(A_84, k4_xboole_0(A_84, B_85))=k3_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.41/1.64  tff(c_632, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k3_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_617])).
% 3.41/1.64  tff(c_635, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_632])).
% 3.41/1.64  tff(c_18, plain, (![A_12, B_13]: (k6_subset_1(A_12, B_13)=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.41/1.64  tff(c_32, plain, (![A_22, B_24]: (k6_subset_1(k4_relat_1(A_22), k4_relat_1(B_24))=k4_relat_1(k6_subset_1(A_22, B_24)) | ~v1_relat_1(B_24) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.41/1.64  tff(c_862, plain, (![A_103, B_104]: (k4_xboole_0(k4_relat_1(A_103), k4_relat_1(B_104))=k4_relat_1(k4_xboole_0(A_103, B_104)) | ~v1_relat_1(B_104) | ~v1_relat_1(A_103))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_32])).
% 3.41/1.64  tff(c_872, plain, (![B_104]: (k4_relat_1(k4_xboole_0(B_104, B_104))=k1_xboole_0 | ~v1_relat_1(B_104) | ~v1_relat_1(B_104))), inference(superposition, [status(thm), theory('equality')], [c_862, c_635])).
% 3.41/1.64  tff(c_891, plain, (![B_104]: (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_104) | ~v1_relat_1(B_104))), inference(demodulation, [status(thm), theory('equality')], [c_635, c_872])).
% 3.41/1.64  tff(c_895, plain, (![B_105]: (~v1_relat_1(B_105) | ~v1_relat_1(B_105))), inference(splitLeft, [status(thm)], [c_891])).
% 3.41/1.64  tff(c_901, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_68, c_895])).
% 3.41/1.64  tff(c_909, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_901])).
% 3.41/1.64  tff(c_910, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_891])).
% 3.41/1.64  tff(c_36, plain, (![B_30, A_28]: (k5_relat_1(k4_relat_1(B_30), k4_relat_1(A_28))=k4_relat_1(k5_relat_1(A_28, B_30)) | ~v1_relat_1(B_30) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.41/1.64  tff(c_920, plain, (![A_28]: (k5_relat_1(k1_xboole_0, k4_relat_1(A_28))=k4_relat_1(k5_relat_1(A_28, k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_28))), inference(superposition, [status(thm), theory('equality')], [c_910, c_36])).
% 3.41/1.64  tff(c_998, plain, (![A_108]: (k5_relat_1(k1_xboole_0, k4_relat_1(A_108))=k4_relat_1(k5_relat_1(A_108, k1_xboole_0)) | ~v1_relat_1(A_108))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_920])).
% 3.41/1.64  tff(c_24, plain, (![A_17]: (v1_relat_1(k4_relat_1(A_17)) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.41/1.64  tff(c_765, plain, (![A_97, B_98]: (k1_relat_1(k5_relat_1(A_97, B_98))=k1_relat_1(A_97) | ~r1_tarski(k2_relat_1(A_97), k1_relat_1(B_98)) | ~v1_relat_1(B_98) | ~v1_relat_1(A_97))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.41/1.64  tff(c_771, plain, (![B_98]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_98))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_98)) | ~v1_relat_1(B_98) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_38, c_765])).
% 3.41/1.64  tff(c_776, plain, (![B_99]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_99))=k1_xboole_0 | ~v1_relat_1(B_99))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_8, c_40, c_771])).
% 3.41/1.64  tff(c_785, plain, (![B_99]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_99)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_99)) | ~v1_relat_1(B_99))), inference(superposition, [status(thm), theory('equality')], [c_776, c_28])).
% 3.41/1.64  tff(c_798, plain, (![B_100]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_100)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_100)) | ~v1_relat_1(B_100))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_785])).
% 3.41/1.64  tff(c_812, plain, (![B_101]: (k5_relat_1(k1_xboole_0, B_101)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_101)) | ~v1_relat_1(B_101))), inference(resolution, [status(thm)], [c_798, c_4])).
% 3.41/1.64  tff(c_816, plain, (![B_19]: (k5_relat_1(k1_xboole_0, B_19)=k1_xboole_0 | ~v1_relat_1(B_19) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_812])).
% 3.41/1.64  tff(c_825, plain, (![B_102]: (k5_relat_1(k1_xboole_0, B_102)=k1_xboole_0 | ~v1_relat_1(B_102))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_816])).
% 3.41/1.64  tff(c_839, plain, (![A_17]: (k5_relat_1(k1_xboole_0, k4_relat_1(A_17))=k1_xboole_0 | ~v1_relat_1(A_17))), inference(resolution, [status(thm)], [c_24, c_825])).
% 3.41/1.64  tff(c_1032, plain, (![A_109]: (k4_relat_1(k5_relat_1(A_109, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_109) | ~v1_relat_1(A_109))), inference(superposition, [status(thm), theory('equality')], [c_998, c_839])).
% 3.41/1.64  tff(c_30, plain, (![A_21]: (k4_relat_1(k4_relat_1(A_21))=A_21 | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.41/1.64  tff(c_1059, plain, (![A_109]: (k5_relat_1(A_109, k1_xboole_0)=k4_relat_1(k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_109, k1_xboole_0)) | ~v1_relat_1(A_109) | ~v1_relat_1(A_109))), inference(superposition, [status(thm), theory('equality')], [c_1032, c_30])).
% 3.41/1.64  tff(c_1520, plain, (![A_122]: (k5_relat_1(A_122, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_122, k1_xboole_0)) | ~v1_relat_1(A_122) | ~v1_relat_1(A_122))), inference(demodulation, [status(thm), theory('equality')], [c_910, c_1059])).
% 3.41/1.64  tff(c_1530, plain, (![A_18]: (k5_relat_1(A_18, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_18))), inference(resolution, [status(thm)], [c_26, c_1520])).
% 3.41/1.64  tff(c_1536, plain, (![A_123]: (k5_relat_1(A_123, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_123))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1530])).
% 3.41/1.64  tff(c_1557, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_1536])).
% 3.41/1.64  tff(c_1568, plain, $false, inference(negUnitSimplification, [status(thm)], [c_544, c_1557])).
% 3.41/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.41/1.64  
% 3.41/1.64  Inference rules
% 3.41/1.64  ----------------------
% 3.41/1.64  #Ref     : 0
% 3.41/1.64  #Sup     : 361
% 3.41/1.64  #Fact    : 0
% 3.41/1.64  #Define  : 0
% 3.41/1.64  #Split   : 3
% 3.41/1.64  #Chain   : 0
% 3.41/1.64  #Close   : 0
% 3.41/1.64  
% 3.41/1.64  Ordering : KBO
% 3.41/1.64  
% 3.41/1.64  Simplification rules
% 3.41/1.64  ----------------------
% 3.41/1.64  #Subsume      : 7
% 3.41/1.64  #Demod        : 327
% 3.41/1.64  #Tautology    : 216
% 3.41/1.64  #SimpNegUnit  : 2
% 3.41/1.64  #BackRed      : 0
% 3.41/1.64  
% 3.41/1.64  #Partial instantiations: 0
% 3.41/1.64  #Strategies tried      : 1
% 3.41/1.64  
% 3.41/1.64  Timing (in seconds)
% 3.41/1.64  ----------------------
% 3.41/1.65  Preprocessing        : 0.36
% 3.41/1.65  Parsing              : 0.19
% 3.41/1.65  CNF conversion       : 0.02
% 3.41/1.65  Main loop            : 0.48
% 3.41/1.65  Inferencing          : 0.18
% 3.41/1.65  Reduction            : 0.15
% 3.41/1.65  Demodulation         : 0.11
% 3.41/1.65  BG Simplification    : 0.03
% 3.41/1.65  Subsumption          : 0.08
% 3.41/1.65  Abstraction          : 0.03
% 3.41/1.65  MUC search           : 0.00
% 3.41/1.65  Cooper               : 0.00
% 3.41/1.65  Total                : 0.88
% 3.41/1.65  Index Insertion      : 0.00
% 3.41/1.65  Index Deletion       : 0.00
% 3.41/1.65  Index Matching       : 0.00
% 3.41/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
