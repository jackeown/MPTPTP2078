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
% DateTime   : Thu Dec  3 09:59:03 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 212 expanded)
%              Number of leaves         :   38 (  85 expanded)
%              Depth                    :   14
%              Number of atoms          :  160 ( 328 expanded)
%              Number of equality atoms :   59 ( 142 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_34,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_100,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_36,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_38,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k6_subset_1(A,B)) = k6_subset_1(k4_relat_1(A),k4_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(c_52,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_79,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_54,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_74,plain,(
    ! [A_37] :
      ( v1_relat_1(A_37)
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_78,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_74])).

tff(c_36,plain,(
    ! [A_21,B_22] :
      ( v1_relat_1(k5_relat_1(A_21,B_22))
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_10,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_26,plain,(
    ! [B_14] : k2_zfmisc_1(k1_xboole_0,B_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_50,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_305,plain,(
    ! [A_66,B_67] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_66,B_67)),k1_relat_1(A_66))
      | ~ v1_relat_1(B_67)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_310,plain,(
    ! [B_67] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_67)),k1_xboole_0)
      | ~ v1_relat_1(B_67)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_305])).

tff(c_314,plain,(
    ! [B_68] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_68)),k1_xboole_0)
      | ~ v1_relat_1(B_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_310])).

tff(c_12,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_159,plain,(
    ! [B_49,A_50] :
      ( B_49 = A_50
      | ~ r1_tarski(B_49,A_50)
      | ~ r1_tarski(A_50,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_168,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_159])).

tff(c_324,plain,(
    ! [B_69] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_69)) = k1_xboole_0
      | ~ v1_relat_1(B_69) ) ),
    inference(resolution,[status(thm)],[c_314,c_168])).

tff(c_40,plain,(
    ! [A_24] :
      ( k3_xboole_0(A_24,k2_zfmisc_1(k1_relat_1(A_24),k2_relat_1(A_24))) = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_339,plain,(
    ! [B_69] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_69),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_69)))) = k5_relat_1(k1_xboole_0,B_69)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_69))
      | ~ v1_relat_1(B_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_40])).

tff(c_350,plain,(
    ! [B_70] :
      ( k5_relat_1(k1_xboole_0,B_70) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_70))
      | ~ v1_relat_1(B_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_26,c_339])).

tff(c_354,plain,(
    ! [B_22] :
      ( k5_relat_1(k1_xboole_0,B_22) = k1_xboole_0
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_36,c_350])).

tff(c_386,plain,(
    ! [B_73] :
      ( k5_relat_1(k1_xboole_0,B_73) = k1_xboole_0
      | ~ v1_relat_1(B_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_354])).

tff(c_398,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_386])).

tff(c_405,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_398])).

tff(c_406,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_34,plain,(
    ! [A_20] :
      ( v1_relat_1(k4_relat_1(A_20))
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_14,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_507,plain,(
    ! [A_89,B_90] : k4_xboole_0(A_89,k4_xboole_0(A_89,B_90)) = k3_xboole_0(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_522,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k3_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_507])).

tff(c_525,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_522])).

tff(c_28,plain,(
    ! [A_15,B_16] : k6_subset_1(A_15,B_16) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_42,plain,(
    ! [A_25,B_27] :
      ( k6_subset_1(k4_relat_1(A_25),k4_relat_1(B_27)) = k4_relat_1(k6_subset_1(A_25,B_27))
      | ~ v1_relat_1(B_27)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_754,plain,(
    ! [A_110,B_111] :
      ( k4_xboole_0(k4_relat_1(A_110),k4_relat_1(B_111)) = k4_relat_1(k4_xboole_0(A_110,B_111))
      | ~ v1_relat_1(B_111)
      | ~ v1_relat_1(A_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_42])).

tff(c_761,plain,(
    ! [B_111] :
      ( k4_relat_1(k4_xboole_0(B_111,B_111)) = k1_xboole_0
      | ~ v1_relat_1(B_111)
      | ~ v1_relat_1(B_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_754,c_525])).

tff(c_779,plain,(
    ! [B_111] :
      ( k4_relat_1(k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_111)
      | ~ v1_relat_1(B_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_761])).

tff(c_807,plain,(
    ! [B_112] :
      ( ~ v1_relat_1(B_112)
      | ~ v1_relat_1(B_112) ) ),
    inference(splitLeft,[status(thm)],[c_779])).

tff(c_813,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_78,c_807])).

tff(c_821,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_813])).

tff(c_822,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_779])).

tff(c_643,plain,(
    ! [A_102,B_103] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_102,B_103)),k1_relat_1(A_102))
      | ~ v1_relat_1(B_103)
      | ~ v1_relat_1(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_651,plain,(
    ! [B_103] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_103)),k1_xboole_0)
      | ~ v1_relat_1(B_103)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_643])).

tff(c_678,plain,(
    ! [B_106] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_106)),k1_xboole_0)
      | ~ v1_relat_1(B_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_651])).

tff(c_497,plain,(
    ! [B_87,A_88] :
      ( B_87 = A_88
      | ~ r1_tarski(B_87,A_88)
      | ~ r1_tarski(A_88,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_506,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_497])).

tff(c_693,plain,(
    ! [B_107] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_107)) = k1_xboole_0
      | ~ v1_relat_1(B_107) ) ),
    inference(resolution,[status(thm)],[c_678,c_506])).

tff(c_708,plain,(
    ! [B_107] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_107),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_107)))) = k5_relat_1(k1_xboole_0,B_107)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_107))
      | ~ v1_relat_1(B_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_693,c_40])).

tff(c_723,plain,(
    ! [B_108] :
      ( k5_relat_1(k1_xboole_0,B_108) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_108))
      | ~ v1_relat_1(B_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_26,c_708])).

tff(c_727,plain,(
    ! [B_22] :
      ( k5_relat_1(k1_xboole_0,B_22) = k1_xboole_0
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_36,c_723])).

tff(c_736,plain,(
    ! [B_109] :
      ( k5_relat_1(k1_xboole_0,B_109) = k1_xboole_0
      | ~ v1_relat_1(B_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_727])).

tff(c_750,plain,(
    ! [A_20] :
      ( k5_relat_1(k1_xboole_0,k4_relat_1(A_20)) = k1_xboole_0
      | ~ v1_relat_1(A_20) ) ),
    inference(resolution,[status(thm)],[c_34,c_736])).

tff(c_38,plain,(
    ! [A_23] :
      ( k4_relat_1(k4_relat_1(A_23)) = A_23
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_46,plain,(
    ! [B_33,A_31] :
      ( k5_relat_1(k4_relat_1(B_33),k4_relat_1(A_31)) = k4_relat_1(k5_relat_1(A_31,B_33))
      | ~ v1_relat_1(B_33)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_868,plain,(
    ! [B_33] :
      ( k5_relat_1(k4_relat_1(B_33),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,B_33))
      | ~ v1_relat_1(B_33)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_822,c_46])).

tff(c_893,plain,(
    ! [B_114] :
      ( k5_relat_1(k4_relat_1(B_114),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,B_114))
      | ~ v1_relat_1(B_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_868])).

tff(c_1503,plain,(
    ! [A_133] :
      ( k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(A_133))) = k5_relat_1(A_133,k1_xboole_0)
      | ~ v1_relat_1(k4_relat_1(A_133))
      | ~ v1_relat_1(A_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_893])).

tff(c_1569,plain,(
    ! [A_20] :
      ( k5_relat_1(A_20,k1_xboole_0) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k4_relat_1(A_20))
      | ~ v1_relat_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_750,c_1503])).

tff(c_1581,plain,(
    ! [A_134] :
      ( k5_relat_1(A_134,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k4_relat_1(A_134))
      | ~ v1_relat_1(A_134)
      | ~ v1_relat_1(A_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_822,c_1569])).

tff(c_1617,plain,(
    ! [A_135] :
      ( k5_relat_1(A_135,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_135) ) ),
    inference(resolution,[status(thm)],[c_34,c_1581])).

tff(c_1638,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_1617])).

tff(c_1649,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_406,c_1638])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:40:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.21/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.49  
% 3.21/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.49  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 3.21/1.49  
% 3.21/1.49  %Foreground sorts:
% 3.21/1.49  
% 3.21/1.49  
% 3.21/1.49  %Background operators:
% 3.21/1.49  
% 3.21/1.49  
% 3.21/1.49  %Foreground operators:
% 3.21/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.21/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.21/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.21/1.49  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.21/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.21/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.21/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.21/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.21/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.21/1.49  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.21/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.21/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.21/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.21/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.21/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.21/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.21/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.21/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.21/1.49  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.21/1.49  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.21/1.49  
% 3.39/1.51  tff(f_107, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 3.39/1.51  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.39/1.51  tff(f_58, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.39/1.51  tff(f_68, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.39/1.51  tff(f_34, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.39/1.51  tff(f_50, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.39/1.51  tff(f_100, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.39/1.51  tff(f_90, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 3.39/1.51  tff(f_36, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.39/1.51  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.39/1.51  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 3.39/1.51  tff(f_62, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 3.39/1.51  tff(f_38, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.39/1.51  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.39/1.51  tff(f_52, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.39/1.51  tff(f_83, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k6_subset_1(A, B)) = k6_subset_1(k4_relat_1(A), k4_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_relat_1)).
% 3.39/1.51  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 3.39/1.51  tff(f_97, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 3.39/1.51  tff(c_52, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.39/1.51  tff(c_79, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_52])).
% 3.39/1.51  tff(c_54, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.39/1.51  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.39/1.51  tff(c_74, plain, (![A_37]: (v1_relat_1(A_37) | ~v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.39/1.51  tff(c_78, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_74])).
% 3.39/1.51  tff(c_36, plain, (![A_21, B_22]: (v1_relat_1(k5_relat_1(A_21, B_22)) | ~v1_relat_1(B_22) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.39/1.51  tff(c_10, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.39/1.51  tff(c_26, plain, (![B_14]: (k2_zfmisc_1(k1_xboole_0, B_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.39/1.51  tff(c_50, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.39/1.51  tff(c_305, plain, (![A_66, B_67]: (r1_tarski(k1_relat_1(k5_relat_1(A_66, B_67)), k1_relat_1(A_66)) | ~v1_relat_1(B_67) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.39/1.51  tff(c_310, plain, (![B_67]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_67)), k1_xboole_0) | ~v1_relat_1(B_67) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_50, c_305])).
% 3.39/1.51  tff(c_314, plain, (![B_68]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_68)), k1_xboole_0) | ~v1_relat_1(B_68))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_310])).
% 3.39/1.51  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.39/1.51  tff(c_159, plain, (![B_49, A_50]: (B_49=A_50 | ~r1_tarski(B_49, A_50) | ~r1_tarski(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.39/1.51  tff(c_168, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_159])).
% 3.39/1.51  tff(c_324, plain, (![B_69]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_69))=k1_xboole_0 | ~v1_relat_1(B_69))), inference(resolution, [status(thm)], [c_314, c_168])).
% 3.39/1.51  tff(c_40, plain, (![A_24]: (k3_xboole_0(A_24, k2_zfmisc_1(k1_relat_1(A_24), k2_relat_1(A_24)))=A_24 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.39/1.51  tff(c_339, plain, (![B_69]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_69), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_69))))=k5_relat_1(k1_xboole_0, B_69) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_69)) | ~v1_relat_1(B_69))), inference(superposition, [status(thm), theory('equality')], [c_324, c_40])).
% 3.39/1.51  tff(c_350, plain, (![B_70]: (k5_relat_1(k1_xboole_0, B_70)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_70)) | ~v1_relat_1(B_70))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_26, c_339])).
% 3.39/1.51  tff(c_354, plain, (![B_22]: (k5_relat_1(k1_xboole_0, B_22)=k1_xboole_0 | ~v1_relat_1(B_22) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_36, c_350])).
% 3.39/1.51  tff(c_386, plain, (![B_73]: (k5_relat_1(k1_xboole_0, B_73)=k1_xboole_0 | ~v1_relat_1(B_73))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_354])).
% 3.39/1.51  tff(c_398, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_386])).
% 3.39/1.51  tff(c_405, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_398])).
% 3.39/1.51  tff(c_406, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 3.39/1.51  tff(c_34, plain, (![A_20]: (v1_relat_1(k4_relat_1(A_20)) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.39/1.51  tff(c_14, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.39/1.51  tff(c_507, plain, (![A_89, B_90]: (k4_xboole_0(A_89, k4_xboole_0(A_89, B_90))=k3_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.39/1.51  tff(c_522, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k3_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_507])).
% 3.39/1.51  tff(c_525, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_522])).
% 3.39/1.51  tff(c_28, plain, (![A_15, B_16]: (k6_subset_1(A_15, B_16)=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.39/1.51  tff(c_42, plain, (![A_25, B_27]: (k6_subset_1(k4_relat_1(A_25), k4_relat_1(B_27))=k4_relat_1(k6_subset_1(A_25, B_27)) | ~v1_relat_1(B_27) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.39/1.51  tff(c_754, plain, (![A_110, B_111]: (k4_xboole_0(k4_relat_1(A_110), k4_relat_1(B_111))=k4_relat_1(k4_xboole_0(A_110, B_111)) | ~v1_relat_1(B_111) | ~v1_relat_1(A_110))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_42])).
% 3.39/1.51  tff(c_761, plain, (![B_111]: (k4_relat_1(k4_xboole_0(B_111, B_111))=k1_xboole_0 | ~v1_relat_1(B_111) | ~v1_relat_1(B_111))), inference(superposition, [status(thm), theory('equality')], [c_754, c_525])).
% 3.39/1.51  tff(c_779, plain, (![B_111]: (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_111) | ~v1_relat_1(B_111))), inference(demodulation, [status(thm), theory('equality')], [c_525, c_761])).
% 3.39/1.51  tff(c_807, plain, (![B_112]: (~v1_relat_1(B_112) | ~v1_relat_1(B_112))), inference(splitLeft, [status(thm)], [c_779])).
% 3.39/1.51  tff(c_813, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_78, c_807])).
% 3.39/1.51  tff(c_821, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_813])).
% 3.39/1.51  tff(c_822, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_779])).
% 3.39/1.51  tff(c_643, plain, (![A_102, B_103]: (r1_tarski(k1_relat_1(k5_relat_1(A_102, B_103)), k1_relat_1(A_102)) | ~v1_relat_1(B_103) | ~v1_relat_1(A_102))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.39/1.51  tff(c_651, plain, (![B_103]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_103)), k1_xboole_0) | ~v1_relat_1(B_103) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_50, c_643])).
% 3.39/1.51  tff(c_678, plain, (![B_106]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_106)), k1_xboole_0) | ~v1_relat_1(B_106))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_651])).
% 3.39/1.51  tff(c_497, plain, (![B_87, A_88]: (B_87=A_88 | ~r1_tarski(B_87, A_88) | ~r1_tarski(A_88, B_87))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.39/1.51  tff(c_506, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_497])).
% 3.39/1.51  tff(c_693, plain, (![B_107]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_107))=k1_xboole_0 | ~v1_relat_1(B_107))), inference(resolution, [status(thm)], [c_678, c_506])).
% 3.39/1.51  tff(c_708, plain, (![B_107]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_107), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_107))))=k5_relat_1(k1_xboole_0, B_107) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_107)) | ~v1_relat_1(B_107))), inference(superposition, [status(thm), theory('equality')], [c_693, c_40])).
% 3.39/1.51  tff(c_723, plain, (![B_108]: (k5_relat_1(k1_xboole_0, B_108)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_108)) | ~v1_relat_1(B_108))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_26, c_708])).
% 3.39/1.51  tff(c_727, plain, (![B_22]: (k5_relat_1(k1_xboole_0, B_22)=k1_xboole_0 | ~v1_relat_1(B_22) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_36, c_723])).
% 3.39/1.51  tff(c_736, plain, (![B_109]: (k5_relat_1(k1_xboole_0, B_109)=k1_xboole_0 | ~v1_relat_1(B_109))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_727])).
% 3.39/1.51  tff(c_750, plain, (![A_20]: (k5_relat_1(k1_xboole_0, k4_relat_1(A_20))=k1_xboole_0 | ~v1_relat_1(A_20))), inference(resolution, [status(thm)], [c_34, c_736])).
% 3.39/1.51  tff(c_38, plain, (![A_23]: (k4_relat_1(k4_relat_1(A_23))=A_23 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.39/1.51  tff(c_46, plain, (![B_33, A_31]: (k5_relat_1(k4_relat_1(B_33), k4_relat_1(A_31))=k4_relat_1(k5_relat_1(A_31, B_33)) | ~v1_relat_1(B_33) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.39/1.51  tff(c_868, plain, (![B_33]: (k5_relat_1(k4_relat_1(B_33), k1_xboole_0)=k4_relat_1(k5_relat_1(k1_xboole_0, B_33)) | ~v1_relat_1(B_33) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_822, c_46])).
% 3.39/1.51  tff(c_893, plain, (![B_114]: (k5_relat_1(k4_relat_1(B_114), k1_xboole_0)=k4_relat_1(k5_relat_1(k1_xboole_0, B_114)) | ~v1_relat_1(B_114))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_868])).
% 3.39/1.51  tff(c_1503, plain, (![A_133]: (k4_relat_1(k5_relat_1(k1_xboole_0, k4_relat_1(A_133)))=k5_relat_1(A_133, k1_xboole_0) | ~v1_relat_1(k4_relat_1(A_133)) | ~v1_relat_1(A_133))), inference(superposition, [status(thm), theory('equality')], [c_38, c_893])).
% 3.39/1.51  tff(c_1569, plain, (![A_20]: (k5_relat_1(A_20, k1_xboole_0)=k4_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(A_20)) | ~v1_relat_1(A_20) | ~v1_relat_1(A_20))), inference(superposition, [status(thm), theory('equality')], [c_750, c_1503])).
% 3.39/1.51  tff(c_1581, plain, (![A_134]: (k5_relat_1(A_134, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k4_relat_1(A_134)) | ~v1_relat_1(A_134) | ~v1_relat_1(A_134))), inference(demodulation, [status(thm), theory('equality')], [c_822, c_1569])).
% 3.39/1.51  tff(c_1617, plain, (![A_135]: (k5_relat_1(A_135, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_135))), inference(resolution, [status(thm)], [c_34, c_1581])).
% 3.39/1.51  tff(c_1638, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_1617])).
% 3.39/1.51  tff(c_1649, plain, $false, inference(negUnitSimplification, [status(thm)], [c_406, c_1638])).
% 3.39/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.51  
% 3.39/1.51  Inference rules
% 3.39/1.51  ----------------------
% 3.39/1.51  #Ref     : 0
% 3.39/1.51  #Sup     : 379
% 3.39/1.51  #Fact    : 0
% 3.39/1.51  #Define  : 0
% 3.39/1.51  #Split   : 2
% 3.39/1.51  #Chain   : 0
% 3.39/1.51  #Close   : 0
% 3.39/1.51  
% 3.39/1.51  Ordering : KBO
% 3.39/1.51  
% 3.39/1.51  Simplification rules
% 3.39/1.51  ----------------------
% 3.39/1.51  #Subsume      : 17
% 3.39/1.51  #Demod        : 318
% 3.39/1.51  #Tautology    : 208
% 3.39/1.51  #SimpNegUnit  : 2
% 3.39/1.51  #BackRed      : 0
% 3.39/1.51  
% 3.39/1.51  #Partial instantiations: 0
% 3.39/1.51  #Strategies tried      : 1
% 3.39/1.51  
% 3.39/1.51  Timing (in seconds)
% 3.39/1.51  ----------------------
% 3.39/1.51  Preprocessing        : 0.31
% 3.39/1.51  Parsing              : 0.17
% 3.39/1.51  CNF conversion       : 0.02
% 3.39/1.51  Main loop            : 0.44
% 3.39/1.51  Inferencing          : 0.16
% 3.39/1.51  Reduction            : 0.14
% 3.39/1.51  Demodulation         : 0.11
% 3.39/1.51  BG Simplification    : 0.02
% 3.39/1.51  Subsumption          : 0.08
% 3.39/1.51  Abstraction          : 0.03
% 3.39/1.51  MUC search           : 0.00
% 3.39/1.51  Cooper               : 0.00
% 3.39/1.51  Total                : 0.78
% 3.39/1.51  Index Insertion      : 0.00
% 3.39/1.51  Index Deletion       : 0.00
% 3.39/1.51  Index Matching       : 0.00
% 3.39/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
