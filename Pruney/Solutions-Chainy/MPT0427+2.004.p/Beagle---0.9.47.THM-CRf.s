%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:56 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 363 expanded)
%              Number of leaves         :   38 ( 134 expanded)
%              Depth                    :   13
%              Number of atoms          :  139 ( 707 expanded)
%              Number of equality atoms :   61 ( 225 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k1_enumset1 > k8_setfam_1 > k6_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_106,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_157,plain,(
    ! [A_62,B_63] : k5_xboole_0(A_62,k3_xboole_0(A_62,B_63)) = k4_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_166,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_157])).

tff(c_169,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_166])).

tff(c_22,plain,(
    ! [B_20] : k4_xboole_0(k1_tarski(B_20),k1_tarski(B_20)) != k1_tarski(B_20) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_170,plain,(
    ! [B_20] : k1_tarski(B_20) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_22])).

tff(c_108,plain,(
    ! [A_54,B_55] :
      ( k2_xboole_0(k1_tarski(A_54),B_55) = B_55
      | ~ r2_hidden(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k1_xboole_0 = A_10
      | k2_xboole_0(A_10,B_11) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_114,plain,(
    ! [A_54,B_55] :
      ( k1_tarski(A_54) = k1_xboole_0
      | k1_xboole_0 != B_55
      | ~ r2_hidden(A_54,B_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_12])).

tff(c_271,plain,(
    ! [B_72,A_73] :
      ( k1_xboole_0 != B_72
      | ~ r2_hidden(A_73,B_72) ) ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_114])).

tff(c_277,plain,(
    ! [A_74] :
      ( k1_xboole_0 != A_74
      | v1_xboole_0(A_74) ) ),
    inference(resolution,[status(thm)],[c_4,c_271])).

tff(c_46,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_40,plain,(
    ! [A_32,B_33] :
      ( m1_subset_1(A_32,k1_zfmisc_1(B_33))
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_120,plain,(
    ! [B_56,A_57] :
      ( v1_xboole_0(B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_57))
      | ~ v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_134,plain,(
    ! [A_58,B_59] :
      ( v1_xboole_0(A_58)
      | ~ v1_xboole_0(B_59)
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(resolution,[status(thm)],[c_40,c_120])).

tff(c_146,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_134])).

tff(c_147,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_287,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_277,c_147])).

tff(c_290,plain,(
    ! [A_75,B_76] :
      ( k6_setfam_1(A_75,B_76) = k1_setfam_1(B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(k1_zfmisc_1(A_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_303,plain,(
    k6_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_290])).

tff(c_387,plain,(
    ! [A_88,B_89] :
      ( k8_setfam_1(A_88,B_89) = k6_setfam_1(A_88,B_89)
      | k1_xboole_0 = B_89
      | ~ m1_subset_1(B_89,k1_zfmisc_1(k1_zfmisc_1(A_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_401,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k6_setfam_1('#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_48,c_387])).

tff(c_407,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_401])).

tff(c_408,plain,(
    k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_287,c_407])).

tff(c_334,plain,(
    ! [A_81,B_82] :
      ( m1_subset_1(k8_setfam_1(A_81,B_82),k1_zfmisc_1(A_81))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(k1_zfmisc_1(A_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_38,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(A_32,B_33)
      | ~ m1_subset_1(A_32,k1_zfmisc_1(B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_348,plain,(
    ! [A_83,B_84] :
      ( r1_tarski(k8_setfam_1(A_83,B_84),A_83)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(k1_zfmisc_1(A_83))) ) ),
    inference(resolution,[status(thm)],[c_334,c_38])).

tff(c_362,plain,(
    r1_tarski(k8_setfam_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_348])).

tff(c_409,plain,(
    r1_tarski(k1_setfam_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_362])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_86,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(A_50,B_51)
      | ~ m1_subset_1(A_50,k1_zfmisc_1(B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_97,plain,(
    r1_tarski('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_86])).

tff(c_302,plain,(
    k6_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_290])).

tff(c_398,plain,
    ( k8_setfam_1('#skF_2','#skF_3') = k6_setfam_1('#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_50,c_387])).

tff(c_405,plain,
    ( k8_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_398])).

tff(c_439,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_405])).

tff(c_182,plain,(
    ! [A_66] :
      ( k8_setfam_1(A_66,k1_xboole_0) = A_66
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_186,plain,(
    ! [A_66] :
      ( k8_setfam_1(A_66,k1_xboole_0) = A_66
      | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(A_66)) ) ),
    inference(resolution,[status(thm)],[c_40,c_182])).

tff(c_531,plain,(
    ! [A_99] :
      ( k8_setfam_1(A_99,'#skF_3') = A_99
      | ~ r1_tarski('#skF_3',k1_zfmisc_1(A_99)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_439,c_439,c_186])).

tff(c_535,plain,(
    k8_setfam_1('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_97,c_531])).

tff(c_44,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),k8_setfam_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_410,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_4'),k8_setfam_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_44])).

tff(c_536,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_535,c_410])).

tff(c_540,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_536])).

tff(c_542,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_405])).

tff(c_42,plain,(
    ! [B_35,A_34] :
      ( r1_tarski(k1_setfam_1(B_35),k1_setfam_1(A_34))
      | k1_xboole_0 = A_34
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_541,plain,(
    k8_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_405])).

tff(c_543,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_4'),k1_setfam_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_410])).

tff(c_566,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_543])).

tff(c_569,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_566])).

tff(c_571,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_542,c_569])).

tff(c_573,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_8,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_581,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_573,c_8])).

tff(c_28,plain,(
    ! [A_24] :
      ( k8_setfam_1(A_24,k1_xboole_0) = A_24
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_666,plain,(
    ! [A_109] :
      ( k8_setfam_1(A_109,'#skF_4') = A_109
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(A_109))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_581,c_581,c_28])).

tff(c_674,plain,(
    k8_setfam_1('#skF_2','#skF_4') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_48,c_666])).

tff(c_572,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_577,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_572,c_8])).

tff(c_598,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_581,c_577])).

tff(c_605,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),k8_setfam_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_598,c_44])).

tff(c_676,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_674,c_674,c_605])).

tff(c_821,plain,(
    ! [A_126,B_127] :
      ( m1_subset_1(k8_setfam_1(A_126,B_127),k1_zfmisc_1(A_126))
      | ~ m1_subset_1(B_127,k1_zfmisc_1(k1_zfmisc_1(A_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_834,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_674,c_821])).

tff(c_839,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_834])).

tff(c_845,plain,(
    r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_839,c_38])).

tff(c_850,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_676,c_845])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:40:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.03/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.03/1.49  
% 3.03/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.03/1.50  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k1_enumset1 > k8_setfam_1 > k6_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.03/1.50  
% 3.03/1.50  %Foreground sorts:
% 3.03/1.50  
% 3.03/1.50  
% 3.03/1.50  %Background operators:
% 3.03/1.50  
% 3.03/1.50  
% 3.03/1.50  %Foreground operators:
% 3.03/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.03/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.03/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.03/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.03/1.50  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.03/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.03/1.50  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 3.03/1.50  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.03/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.03/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.03/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.03/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.03/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.03/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.03/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.03/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.03/1.50  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 3.03/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.03/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.03/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.03/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.03/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.03/1.50  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.03/1.50  
% 3.21/1.52  tff(f_106, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_setfam_1)).
% 3.21/1.52  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.21/1.52  tff(f_45, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.21/1.52  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.21/1.52  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.21/1.52  tff(f_58, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.21/1.52  tff(f_53, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 3.21/1.52  tff(f_43, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_xboole_1)).
% 3.21/1.52  tff(f_90, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.21/1.52  tff(f_65, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.21/1.52  tff(f_84, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 3.21/1.52  tff(f_76, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 3.21/1.52  tff(f_80, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 3.21/1.52  tff(f_96, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 3.21/1.52  tff(f_37, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.21/1.52  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.21/1.52  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.21/1.52  tff(c_14, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.21/1.52  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.21/1.52  tff(c_157, plain, (![A_62, B_63]: (k5_xboole_0(A_62, k3_xboole_0(A_62, B_63))=k4_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.21/1.52  tff(c_166, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_157])).
% 3.21/1.52  tff(c_169, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_166])).
% 3.21/1.52  tff(c_22, plain, (![B_20]: (k4_xboole_0(k1_tarski(B_20), k1_tarski(B_20))!=k1_tarski(B_20))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.21/1.52  tff(c_170, plain, (![B_20]: (k1_tarski(B_20)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_169, c_22])).
% 3.21/1.52  tff(c_108, plain, (![A_54, B_55]: (k2_xboole_0(k1_tarski(A_54), B_55)=B_55 | ~r2_hidden(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.21/1.52  tff(c_12, plain, (![A_10, B_11]: (k1_xboole_0=A_10 | k2_xboole_0(A_10, B_11)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.21/1.52  tff(c_114, plain, (![A_54, B_55]: (k1_tarski(A_54)=k1_xboole_0 | k1_xboole_0!=B_55 | ~r2_hidden(A_54, B_55))), inference(superposition, [status(thm), theory('equality')], [c_108, c_12])).
% 3.21/1.52  tff(c_271, plain, (![B_72, A_73]: (k1_xboole_0!=B_72 | ~r2_hidden(A_73, B_72))), inference(negUnitSimplification, [status(thm)], [c_170, c_114])).
% 3.21/1.52  tff(c_277, plain, (![A_74]: (k1_xboole_0!=A_74 | v1_xboole_0(A_74))), inference(resolution, [status(thm)], [c_4, c_271])).
% 3.21/1.52  tff(c_46, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.21/1.52  tff(c_40, plain, (![A_32, B_33]: (m1_subset_1(A_32, k1_zfmisc_1(B_33)) | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.21/1.52  tff(c_120, plain, (![B_56, A_57]: (v1_xboole_0(B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(A_57)) | ~v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.21/1.52  tff(c_134, plain, (![A_58, B_59]: (v1_xboole_0(A_58) | ~v1_xboole_0(B_59) | ~r1_tarski(A_58, B_59))), inference(resolution, [status(thm)], [c_40, c_120])).
% 3.21/1.52  tff(c_146, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_46, c_134])).
% 3.21/1.52  tff(c_147, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_146])).
% 3.21/1.52  tff(c_287, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_277, c_147])).
% 3.21/1.52  tff(c_290, plain, (![A_75, B_76]: (k6_setfam_1(A_75, B_76)=k1_setfam_1(B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(k1_zfmisc_1(A_75))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.21/1.52  tff(c_303, plain, (k6_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_290])).
% 3.21/1.52  tff(c_387, plain, (![A_88, B_89]: (k8_setfam_1(A_88, B_89)=k6_setfam_1(A_88, B_89) | k1_xboole_0=B_89 | ~m1_subset_1(B_89, k1_zfmisc_1(k1_zfmisc_1(A_88))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.21/1.52  tff(c_401, plain, (k8_setfam_1('#skF_2', '#skF_4')=k6_setfam_1('#skF_2', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_48, c_387])).
% 3.21/1.52  tff(c_407, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_303, c_401])).
% 3.21/1.52  tff(c_408, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_287, c_407])).
% 3.21/1.52  tff(c_334, plain, (![A_81, B_82]: (m1_subset_1(k8_setfam_1(A_81, B_82), k1_zfmisc_1(A_81)) | ~m1_subset_1(B_82, k1_zfmisc_1(k1_zfmisc_1(A_81))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.21/1.52  tff(c_38, plain, (![A_32, B_33]: (r1_tarski(A_32, B_33) | ~m1_subset_1(A_32, k1_zfmisc_1(B_33)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.21/1.52  tff(c_348, plain, (![A_83, B_84]: (r1_tarski(k8_setfam_1(A_83, B_84), A_83) | ~m1_subset_1(B_84, k1_zfmisc_1(k1_zfmisc_1(A_83))))), inference(resolution, [status(thm)], [c_334, c_38])).
% 3.21/1.52  tff(c_362, plain, (r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_48, c_348])).
% 3.21/1.52  tff(c_409, plain, (r1_tarski(k1_setfam_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_408, c_362])).
% 3.21/1.52  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.21/1.52  tff(c_86, plain, (![A_50, B_51]: (r1_tarski(A_50, B_51) | ~m1_subset_1(A_50, k1_zfmisc_1(B_51)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.21/1.52  tff(c_97, plain, (r1_tarski('#skF_3', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_50, c_86])).
% 3.21/1.52  tff(c_302, plain, (k6_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_290])).
% 3.21/1.52  tff(c_398, plain, (k8_setfam_1('#skF_2', '#skF_3')=k6_setfam_1('#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_50, c_387])).
% 3.21/1.52  tff(c_405, plain, (k8_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_302, c_398])).
% 3.21/1.52  tff(c_439, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_405])).
% 3.21/1.52  tff(c_182, plain, (![A_66]: (k8_setfam_1(A_66, k1_xboole_0)=A_66 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_66))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.21/1.52  tff(c_186, plain, (![A_66]: (k8_setfam_1(A_66, k1_xboole_0)=A_66 | ~r1_tarski(k1_xboole_0, k1_zfmisc_1(A_66)))), inference(resolution, [status(thm)], [c_40, c_182])).
% 3.21/1.52  tff(c_531, plain, (![A_99]: (k8_setfam_1(A_99, '#skF_3')=A_99 | ~r1_tarski('#skF_3', k1_zfmisc_1(A_99)))), inference(demodulation, [status(thm), theory('equality')], [c_439, c_439, c_186])).
% 3.21/1.52  tff(c_535, plain, (k8_setfam_1('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_97, c_531])).
% 3.21/1.52  tff(c_44, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), k8_setfam_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.21/1.52  tff(c_410, plain, (~r1_tarski(k1_setfam_1('#skF_4'), k8_setfam_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_408, c_44])).
% 3.21/1.52  tff(c_536, plain, (~r1_tarski(k1_setfam_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_535, c_410])).
% 3.21/1.52  tff(c_540, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_409, c_536])).
% 3.21/1.52  tff(c_542, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_405])).
% 3.21/1.52  tff(c_42, plain, (![B_35, A_34]: (r1_tarski(k1_setfam_1(B_35), k1_setfam_1(A_34)) | k1_xboole_0=A_34 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.21/1.52  tff(c_541, plain, (k8_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_405])).
% 3.21/1.52  tff(c_543, plain, (~r1_tarski(k1_setfam_1('#skF_4'), k1_setfam_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_541, c_410])).
% 3.21/1.52  tff(c_566, plain, (k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_543])).
% 3.21/1.52  tff(c_569, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_566])).
% 3.21/1.52  tff(c_571, plain, $false, inference(negUnitSimplification, [status(thm)], [c_542, c_569])).
% 3.21/1.52  tff(c_573, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_146])).
% 3.21/1.52  tff(c_8, plain, (![A_7]: (k1_xboole_0=A_7 | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.21/1.52  tff(c_581, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_573, c_8])).
% 3.21/1.52  tff(c_28, plain, (![A_24]: (k8_setfam_1(A_24, k1_xboole_0)=A_24 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_24))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.21/1.52  tff(c_666, plain, (![A_109]: (k8_setfam_1(A_109, '#skF_4')=A_109 | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(A_109))))), inference(demodulation, [status(thm), theory('equality')], [c_581, c_581, c_28])).
% 3.21/1.52  tff(c_674, plain, (k8_setfam_1('#skF_2', '#skF_4')='#skF_2'), inference(resolution, [status(thm)], [c_48, c_666])).
% 3.21/1.52  tff(c_572, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_146])).
% 3.21/1.52  tff(c_577, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_572, c_8])).
% 3.21/1.52  tff(c_598, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_581, c_577])).
% 3.21/1.52  tff(c_605, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), k8_setfam_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_598, c_44])).
% 3.21/1.52  tff(c_676, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_674, c_674, c_605])).
% 3.21/1.52  tff(c_821, plain, (![A_126, B_127]: (m1_subset_1(k8_setfam_1(A_126, B_127), k1_zfmisc_1(A_126)) | ~m1_subset_1(B_127, k1_zfmisc_1(k1_zfmisc_1(A_126))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.21/1.52  tff(c_834, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_674, c_821])).
% 3.21/1.52  tff(c_839, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_834])).
% 3.21/1.52  tff(c_845, plain, (r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_839, c_38])).
% 3.21/1.52  tff(c_850, plain, $false, inference(negUnitSimplification, [status(thm)], [c_676, c_845])).
% 3.21/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.52  
% 3.21/1.52  Inference rules
% 3.21/1.52  ----------------------
% 3.21/1.52  #Ref     : 0
% 3.21/1.52  #Sup     : 175
% 3.21/1.52  #Fact    : 0
% 3.21/1.52  #Define  : 0
% 3.21/1.52  #Split   : 4
% 3.21/1.52  #Chain   : 0
% 3.21/1.52  #Close   : 0
% 3.21/1.52  
% 3.21/1.52  Ordering : KBO
% 3.21/1.52  
% 3.21/1.52  Simplification rules
% 3.21/1.52  ----------------------
% 3.21/1.52  #Subsume      : 16
% 3.21/1.52  #Demod        : 80
% 3.21/1.52  #Tautology    : 98
% 3.21/1.52  #SimpNegUnit  : 13
% 3.21/1.52  #BackRed      : 36
% 3.21/1.52  
% 3.21/1.52  #Partial instantiations: 0
% 3.21/1.52  #Strategies tried      : 1
% 3.21/1.52  
% 3.21/1.52  Timing (in seconds)
% 3.21/1.52  ----------------------
% 3.21/1.52  Preprocessing        : 0.33
% 3.21/1.52  Parsing              : 0.18
% 3.21/1.52  CNF conversion       : 0.02
% 3.21/1.52  Main loop            : 0.39
% 3.21/1.52  Inferencing          : 0.15
% 3.21/1.52  Reduction            : 0.12
% 3.21/1.52  Demodulation         : 0.08
% 3.21/1.52  BG Simplification    : 0.02
% 3.21/1.52  Subsumption          : 0.05
% 3.21/1.52  Abstraction          : 0.02
% 3.21/1.52  MUC search           : 0.00
% 3.21/1.52  Cooper               : 0.00
% 3.21/1.52  Total                : 0.76
% 3.21/1.52  Index Insertion      : 0.00
% 3.21/1.52  Index Deletion       : 0.00
% 3.21/1.52  Index Matching       : 0.00
% 3.21/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
