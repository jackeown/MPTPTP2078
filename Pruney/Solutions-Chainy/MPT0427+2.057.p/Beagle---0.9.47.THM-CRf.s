%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:04 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 525 expanded)
%              Number of leaves         :   31 ( 179 expanded)
%              Depth                    :   13
%              Number of atoms          :  179 (1080 expanded)
%              Number of equality atoms :   58 ( 256 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_45,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

tff(c_32,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_92,plain,(
    ! [C_40,B_41,A_42] :
      ( ~ v1_xboole_0(C_40)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(C_40))
      | ~ r2_hidden(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_114,plain,(
    ! [B_44,A_45,A_46] :
      ( ~ v1_xboole_0(B_44)
      | ~ r2_hidden(A_45,A_46)
      | ~ r1_tarski(A_46,B_44) ) ),
    inference(resolution,[status(thm)],[c_22,c_92])).

tff(c_118,plain,(
    ! [B_47,A_48] :
      ( ~ v1_xboole_0(B_47)
      | ~ r1_tarski(A_48,B_47)
      | k1_xboole_0 = A_48 ) ),
    inference(resolution,[status(thm)],[c_2,c_114])).

tff(c_135,plain,
    ( ~ v1_xboole_0('#skF_4')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_32,c_118])).

tff(c_155,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_136,plain,(
    ! [A_49,B_50] :
      ( k6_setfam_1(A_49,B_50) = k1_setfam_1(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(k1_zfmisc_1(A_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_153,plain,(
    k6_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_136])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_194,plain,(
    ! [A_56,C_57,B_58] :
      ( m1_subset_1(A_56,C_57)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(C_57))
      | ~ r2_hidden(A_56,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_207,plain,(
    ! [A_59] :
      ( m1_subset_1(A_59,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_59,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_194])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_223,plain,(
    ! [A_62] :
      ( r1_tarski(A_62,'#skF_2')
      | ~ r2_hidden(A_62,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_207,c_20])).

tff(c_228,plain,
    ( r1_tarski('#skF_1'('#skF_3'),'#skF_2')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2,c_223])).

tff(c_229,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_228])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( k8_setfam_1(A_9,B_10) = k6_setfam_1(A_9,B_10)
      | k1_xboole_0 = B_10
      | ~ m1_subset_1(B_10,k1_zfmisc_1(k1_zfmisc_1(A_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_371,plain,(
    ! [A_77,B_78] :
      ( k8_setfam_1(A_77,B_78) = k6_setfam_1(A_77,B_78)
      | B_78 = '#skF_3'
      | ~ m1_subset_1(B_78,k1_zfmisc_1(k1_zfmisc_1(A_77))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_14])).

tff(c_390,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k6_setfam_1('#skF_2','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34,c_371])).

tff(c_398,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_390])).

tff(c_425,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_398])).

tff(c_10,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_63,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(A_35,B_36)
      | ~ m1_subset_1(A_35,k1_zfmisc_1(B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_79,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(resolution,[status(thm)],[c_10,c_63])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_56,plain,(
    ! [A_29,B_30] : r1_xboole_0(k4_xboole_0(A_29,B_30),B_30) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_59,plain,(
    ! [A_3] : r1_xboole_0(k1_xboole_0,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_56])).

tff(c_81,plain,(
    ! [B_38,A_39] :
      ( ~ r1_xboole_0(B_38,A_39)
      | ~ r1_tarski(B_38,A_39)
      | v1_xboole_0(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_84,plain,(
    ! [A_3] :
      ( ~ r1_tarski(k1_xboole_0,A_3)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_59,c_81])).

tff(c_90,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_84])).

tff(c_234,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_90])).

tff(c_436,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_425,c_234])).

tff(c_439,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_436])).

tff(c_440,plain,(
    k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_398])).

tff(c_12,plain,(
    ! [A_9] :
      ( k8_setfam_1(A_9,k1_xboole_0) = A_9
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_38,plain,(
    ! [A_9] : k8_setfam_1(A_9,k1_xboole_0) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_238,plain,(
    ! [A_9] : k8_setfam_1(A_9,'#skF_3') = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_38])).

tff(c_30,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),k8_setfam_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_322,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_30])).

tff(c_442,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_322])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(k8_setfam_1(A_11,B_12),k1_zfmisc_1(A_11))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(k1_zfmisc_1(A_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_446,plain,
    ( m1_subset_1(k1_setfam_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_16])).

tff(c_450,plain,(
    m1_subset_1(k1_setfam_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_446])).

tff(c_458,plain,(
    r1_tarski(k1_setfam_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_450,c_20])).

tff(c_464,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_442,c_458])).

tff(c_466,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_28,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k1_setfam_1(B_24),k1_setfam_1(A_23))
      | k1_xboole_0 = A_23
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_541,plain,(
    ! [A_90,B_91] :
      ( k8_setfam_1(A_90,B_91) = k6_setfam_1(A_90,B_91)
      | k1_xboole_0 = B_91
      | ~ m1_subset_1(B_91,k1_zfmisc_1(k1_zfmisc_1(A_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_559,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k6_setfam_1('#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34,c_541])).

tff(c_571,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_559])).

tff(c_654,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_571])).

tff(c_663,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_654,c_90])).

tff(c_671,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_663])).

tff(c_672,plain,(
    k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_571])).

tff(c_152,plain,(
    k6_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_136])).

tff(c_556,plain,
    ( k8_setfam_1('#skF_2','#skF_3') = k6_setfam_1('#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_36,c_541])).

tff(c_568,plain,
    ( k8_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_556])).

tff(c_569,plain,(
    k8_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_466,c_568])).

tff(c_575,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),k1_setfam_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_569,c_30])).

tff(c_678,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_4'),k1_setfam_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_672,c_575])).

tff(c_690,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_678])).

tff(c_693,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_690])).

tff(c_695,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_466,c_693])).

tff(c_696,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_800,plain,(
    ! [A_110] :
      ( r2_hidden('#skF_1'(A_110),A_110)
      | A_110 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_696,c_2])).

tff(c_773,plain,(
    ! [A_105,C_106,B_107] :
      ( m1_subset_1(A_105,C_106)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(C_106))
      | ~ r2_hidden(A_105,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_788,plain,(
    ! [A_108] :
      ( m1_subset_1(A_108,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_108,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_773])).

tff(c_798,plain,(
    ! [A_108] :
      ( r1_tarski(A_108,'#skF_2')
      | ~ r2_hidden(A_108,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_788,c_20])).

tff(c_811,plain,
    ( r1_tarski('#skF_1'('#skF_4'),'#skF_2')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_800,c_798])).

tff(c_815,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_811])).

tff(c_704,plain,(
    ! [A_9] : k8_setfam_1(A_9,'#skF_3') = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_696,c_38])).

tff(c_818,plain,(
    ! [A_9] : k8_setfam_1(A_9,'#skF_4') = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_815,c_704])).

tff(c_705,plain,(
    ! [A_8] : m1_subset_1('#skF_3',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_696,c_10])).

tff(c_819,plain,(
    ! [A_8] : m1_subset_1('#skF_4',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_815,c_705])).

tff(c_836,plain,(
    ! [A_111,B_112] :
      ( m1_subset_1(k8_setfam_1(A_111,B_112),k1_zfmisc_1(A_111))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(k1_zfmisc_1(A_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_966,plain,(
    ! [A_132,B_133] :
      ( r1_tarski(k8_setfam_1(A_132,B_133),A_132)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(k1_zfmisc_1(A_132))) ) ),
    inference(resolution,[status(thm)],[c_836,c_20])).

tff(c_969,plain,(
    ! [A_132] : r1_tarski(k8_setfam_1(A_132,'#skF_4'),A_132) ),
    inference(resolution,[status(thm)],[c_819,c_966])).

tff(c_977,plain,(
    ! [A_132] : r1_tarski(A_132,A_132) ),
    inference(demodulation,[status(thm),theory(equality)],[c_818,c_969])).

tff(c_754,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_704,c_30])).

tff(c_872,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_818,c_754])).

tff(c_982,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_977,c_872])).

tff(c_984,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_811])).

tff(c_697,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_1015,plain,(
    ! [A_141,B_142] :
      ( m1_subset_1(k8_setfam_1(A_141,B_142),k1_zfmisc_1(A_141))
      | ~ m1_subset_1(B_142,k1_zfmisc_1(k1_zfmisc_1(A_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1029,plain,(
    ! [A_9] :
      ( m1_subset_1(A_9,k1_zfmisc_1(A_9))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(A_9))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_704,c_1015])).

tff(c_1036,plain,(
    ! [A_143] : m1_subset_1(A_143,k1_zfmisc_1(A_143)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_705,c_1029])).

tff(c_1052,plain,(
    ! [A_144] : r1_tarski(A_144,A_144) ),
    inference(resolution,[status(thm)],[c_1036,c_20])).

tff(c_117,plain,(
    ! [B_44,A_1] :
      ( ~ v1_xboole_0(B_44)
      | ~ r1_tarski(A_1,B_44)
      | k1_xboole_0 = A_1 ) ),
    inference(resolution,[status(thm)],[c_2,c_114])).

tff(c_698,plain,(
    ! [B_44,A_1] :
      ( ~ v1_xboole_0(B_44)
      | ~ r1_tarski(A_1,B_44)
      | A_1 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_696,c_117])).

tff(c_1057,plain,(
    ! [A_145] :
      ( ~ v1_xboole_0(A_145)
      | A_145 = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_1052,c_698])).

tff(c_1063,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_697,c_1057])).

tff(c_1069,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_984,c_1063])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:05:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.98/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.53  
% 2.98/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.53  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.98/1.53  
% 2.98/1.53  %Foreground sorts:
% 2.98/1.53  
% 2.98/1.53  
% 2.98/1.53  %Background operators:
% 2.98/1.53  
% 2.98/1.53  
% 2.98/1.53  %Foreground operators:
% 2.98/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.98/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.98/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.98/1.53  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.98/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.98/1.53  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.98/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.98/1.53  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.98/1.53  tff('#skF_2', type, '#skF_2': $i).
% 2.98/1.53  tff('#skF_3', type, '#skF_3': $i).
% 2.98/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.98/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.98/1.53  tff('#skF_4', type, '#skF_4': $i).
% 2.98/1.53  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.98/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.98/1.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.98/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.98/1.53  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.98/1.53  
% 3.11/1.55  tff(f_99, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_setfam_1)).
% 3.11/1.55  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.11/1.55  tff(f_70, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.11/1.55  tff(f_83, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.11/1.55  tff(f_66, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 3.11/1.55  tff(f_76, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.11/1.55  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 3.11/1.55  tff(f_47, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.11/1.55  tff(f_35, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 3.11/1.55  tff(f_45, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.11/1.55  tff(f_43, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.11/1.55  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 3.11/1.55  tff(f_89, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 3.11/1.55  tff(c_32, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.11/1.55  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.11/1.55  tff(c_22, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.11/1.55  tff(c_92, plain, (![C_40, B_41, A_42]: (~v1_xboole_0(C_40) | ~m1_subset_1(B_41, k1_zfmisc_1(C_40)) | ~r2_hidden(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.11/1.55  tff(c_114, plain, (![B_44, A_45, A_46]: (~v1_xboole_0(B_44) | ~r2_hidden(A_45, A_46) | ~r1_tarski(A_46, B_44))), inference(resolution, [status(thm)], [c_22, c_92])).
% 3.11/1.55  tff(c_118, plain, (![B_47, A_48]: (~v1_xboole_0(B_47) | ~r1_tarski(A_48, B_47) | k1_xboole_0=A_48)), inference(resolution, [status(thm)], [c_2, c_114])).
% 3.11/1.55  tff(c_135, plain, (~v1_xboole_0('#skF_4') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_32, c_118])).
% 3.11/1.55  tff(c_155, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_135])).
% 3.11/1.55  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.11/1.55  tff(c_136, plain, (![A_49, B_50]: (k6_setfam_1(A_49, B_50)=k1_setfam_1(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(k1_zfmisc_1(A_49))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.11/1.55  tff(c_153, plain, (k6_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_136])).
% 3.11/1.55  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.11/1.55  tff(c_194, plain, (![A_56, C_57, B_58]: (m1_subset_1(A_56, C_57) | ~m1_subset_1(B_58, k1_zfmisc_1(C_57)) | ~r2_hidden(A_56, B_58))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.11/1.55  tff(c_207, plain, (![A_59]: (m1_subset_1(A_59, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_59, '#skF_3'))), inference(resolution, [status(thm)], [c_36, c_194])).
% 3.11/1.55  tff(c_20, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.11/1.55  tff(c_223, plain, (![A_62]: (r1_tarski(A_62, '#skF_2') | ~r2_hidden(A_62, '#skF_3'))), inference(resolution, [status(thm)], [c_207, c_20])).
% 3.11/1.55  tff(c_228, plain, (r1_tarski('#skF_1'('#skF_3'), '#skF_2') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2, c_223])).
% 3.11/1.55  tff(c_229, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_228])).
% 3.11/1.55  tff(c_14, plain, (![A_9, B_10]: (k8_setfam_1(A_9, B_10)=k6_setfam_1(A_9, B_10) | k1_xboole_0=B_10 | ~m1_subset_1(B_10, k1_zfmisc_1(k1_zfmisc_1(A_9))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.11/1.55  tff(c_371, plain, (![A_77, B_78]: (k8_setfam_1(A_77, B_78)=k6_setfam_1(A_77, B_78) | B_78='#skF_3' | ~m1_subset_1(B_78, k1_zfmisc_1(k1_zfmisc_1(A_77))))), inference(demodulation, [status(thm), theory('equality')], [c_229, c_14])).
% 3.11/1.55  tff(c_390, plain, (k8_setfam_1('#skF_2', '#skF_4')=k6_setfam_1('#skF_2', '#skF_4') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_34, c_371])).
% 3.11/1.55  tff(c_398, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_153, c_390])).
% 3.11/1.55  tff(c_425, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_398])).
% 3.11/1.55  tff(c_10, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.11/1.55  tff(c_63, plain, (![A_35, B_36]: (r1_tarski(A_35, B_36) | ~m1_subset_1(A_35, k1_zfmisc_1(B_36)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.11/1.55  tff(c_79, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(resolution, [status(thm)], [c_10, c_63])).
% 3.11/1.55  tff(c_4, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.11/1.55  tff(c_56, plain, (![A_29, B_30]: (r1_xboole_0(k4_xboole_0(A_29, B_30), B_30))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.11/1.55  tff(c_59, plain, (![A_3]: (r1_xboole_0(k1_xboole_0, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_56])).
% 3.11/1.55  tff(c_81, plain, (![B_38, A_39]: (~r1_xboole_0(B_38, A_39) | ~r1_tarski(B_38, A_39) | v1_xboole_0(B_38))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.11/1.55  tff(c_84, plain, (![A_3]: (~r1_tarski(k1_xboole_0, A_3) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_59, c_81])).
% 3.11/1.55  tff(c_90, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_79, c_84])).
% 3.11/1.55  tff(c_234, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_229, c_90])).
% 3.11/1.55  tff(c_436, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_425, c_234])).
% 3.11/1.55  tff(c_439, plain, $false, inference(negUnitSimplification, [status(thm)], [c_155, c_436])).
% 3.11/1.55  tff(c_440, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4')), inference(splitRight, [status(thm)], [c_398])).
% 3.11/1.55  tff(c_12, plain, (![A_9]: (k8_setfam_1(A_9, k1_xboole_0)=A_9 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_9))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.11/1.55  tff(c_38, plain, (![A_9]: (k8_setfam_1(A_9, k1_xboole_0)=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 3.11/1.55  tff(c_238, plain, (![A_9]: (k8_setfam_1(A_9, '#skF_3')=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_229, c_38])).
% 3.11/1.55  tff(c_30, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), k8_setfam_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.11/1.55  tff(c_322, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_238, c_30])).
% 3.11/1.55  tff(c_442, plain, (~r1_tarski(k1_setfam_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_440, c_322])).
% 3.11/1.55  tff(c_16, plain, (![A_11, B_12]: (m1_subset_1(k8_setfam_1(A_11, B_12), k1_zfmisc_1(A_11)) | ~m1_subset_1(B_12, k1_zfmisc_1(k1_zfmisc_1(A_11))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.11/1.55  tff(c_446, plain, (m1_subset_1(k1_setfam_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_440, c_16])).
% 3.11/1.55  tff(c_450, plain, (m1_subset_1(k1_setfam_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_446])).
% 3.11/1.55  tff(c_458, plain, (r1_tarski(k1_setfam_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_450, c_20])).
% 3.11/1.55  tff(c_464, plain, $false, inference(negUnitSimplification, [status(thm)], [c_442, c_458])).
% 3.11/1.55  tff(c_466, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_228])).
% 3.11/1.55  tff(c_28, plain, (![B_24, A_23]: (r1_tarski(k1_setfam_1(B_24), k1_setfam_1(A_23)) | k1_xboole_0=A_23 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.11/1.55  tff(c_541, plain, (![A_90, B_91]: (k8_setfam_1(A_90, B_91)=k6_setfam_1(A_90, B_91) | k1_xboole_0=B_91 | ~m1_subset_1(B_91, k1_zfmisc_1(k1_zfmisc_1(A_90))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.11/1.55  tff(c_559, plain, (k8_setfam_1('#skF_2', '#skF_4')=k6_setfam_1('#skF_2', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_34, c_541])).
% 3.11/1.55  tff(c_571, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_153, c_559])).
% 3.11/1.55  tff(c_654, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_571])).
% 3.11/1.55  tff(c_663, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_654, c_90])).
% 3.11/1.55  tff(c_671, plain, $false, inference(negUnitSimplification, [status(thm)], [c_155, c_663])).
% 3.11/1.55  tff(c_672, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4')), inference(splitRight, [status(thm)], [c_571])).
% 3.11/1.55  tff(c_152, plain, (k6_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_136])).
% 3.11/1.55  tff(c_556, plain, (k8_setfam_1('#skF_2', '#skF_3')=k6_setfam_1('#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_36, c_541])).
% 3.11/1.55  tff(c_568, plain, (k8_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_152, c_556])).
% 3.11/1.55  tff(c_569, plain, (k8_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_466, c_568])).
% 3.11/1.55  tff(c_575, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), k1_setfam_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_569, c_30])).
% 3.11/1.55  tff(c_678, plain, (~r1_tarski(k1_setfam_1('#skF_4'), k1_setfam_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_672, c_575])).
% 3.11/1.55  tff(c_690, plain, (k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_678])).
% 3.11/1.55  tff(c_693, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_690])).
% 3.11/1.55  tff(c_695, plain, $false, inference(negUnitSimplification, [status(thm)], [c_466, c_693])).
% 3.11/1.55  tff(c_696, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_135])).
% 3.11/1.55  tff(c_800, plain, (![A_110]: (r2_hidden('#skF_1'(A_110), A_110) | A_110='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_696, c_2])).
% 3.11/1.55  tff(c_773, plain, (![A_105, C_106, B_107]: (m1_subset_1(A_105, C_106) | ~m1_subset_1(B_107, k1_zfmisc_1(C_106)) | ~r2_hidden(A_105, B_107))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.11/1.55  tff(c_788, plain, (![A_108]: (m1_subset_1(A_108, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_108, '#skF_4'))), inference(resolution, [status(thm)], [c_34, c_773])).
% 3.11/1.55  tff(c_798, plain, (![A_108]: (r1_tarski(A_108, '#skF_2') | ~r2_hidden(A_108, '#skF_4'))), inference(resolution, [status(thm)], [c_788, c_20])).
% 3.11/1.55  tff(c_811, plain, (r1_tarski('#skF_1'('#skF_4'), '#skF_2') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_800, c_798])).
% 3.11/1.55  tff(c_815, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_811])).
% 3.11/1.55  tff(c_704, plain, (![A_9]: (k8_setfam_1(A_9, '#skF_3')=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_696, c_38])).
% 3.11/1.55  tff(c_818, plain, (![A_9]: (k8_setfam_1(A_9, '#skF_4')=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_815, c_704])).
% 3.11/1.55  tff(c_705, plain, (![A_8]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_696, c_10])).
% 3.11/1.55  tff(c_819, plain, (![A_8]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_815, c_705])).
% 3.11/1.55  tff(c_836, plain, (![A_111, B_112]: (m1_subset_1(k8_setfam_1(A_111, B_112), k1_zfmisc_1(A_111)) | ~m1_subset_1(B_112, k1_zfmisc_1(k1_zfmisc_1(A_111))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.11/1.55  tff(c_966, plain, (![A_132, B_133]: (r1_tarski(k8_setfam_1(A_132, B_133), A_132) | ~m1_subset_1(B_133, k1_zfmisc_1(k1_zfmisc_1(A_132))))), inference(resolution, [status(thm)], [c_836, c_20])).
% 3.11/1.55  tff(c_969, plain, (![A_132]: (r1_tarski(k8_setfam_1(A_132, '#skF_4'), A_132))), inference(resolution, [status(thm)], [c_819, c_966])).
% 3.11/1.55  tff(c_977, plain, (![A_132]: (r1_tarski(A_132, A_132))), inference(demodulation, [status(thm), theory('equality')], [c_818, c_969])).
% 3.11/1.55  tff(c_754, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_704, c_30])).
% 3.11/1.55  tff(c_872, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_818, c_754])).
% 3.11/1.55  tff(c_982, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_977, c_872])).
% 3.11/1.55  tff(c_984, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_811])).
% 3.11/1.55  tff(c_697, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_135])).
% 3.11/1.55  tff(c_1015, plain, (![A_141, B_142]: (m1_subset_1(k8_setfam_1(A_141, B_142), k1_zfmisc_1(A_141)) | ~m1_subset_1(B_142, k1_zfmisc_1(k1_zfmisc_1(A_141))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.11/1.55  tff(c_1029, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(A_9))))), inference(superposition, [status(thm), theory('equality')], [c_704, c_1015])).
% 3.11/1.55  tff(c_1036, plain, (![A_143]: (m1_subset_1(A_143, k1_zfmisc_1(A_143)))), inference(demodulation, [status(thm), theory('equality')], [c_705, c_1029])).
% 3.11/1.55  tff(c_1052, plain, (![A_144]: (r1_tarski(A_144, A_144))), inference(resolution, [status(thm)], [c_1036, c_20])).
% 3.11/1.55  tff(c_117, plain, (![B_44, A_1]: (~v1_xboole_0(B_44) | ~r1_tarski(A_1, B_44) | k1_xboole_0=A_1)), inference(resolution, [status(thm)], [c_2, c_114])).
% 3.11/1.55  tff(c_698, plain, (![B_44, A_1]: (~v1_xboole_0(B_44) | ~r1_tarski(A_1, B_44) | A_1='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_696, c_117])).
% 3.11/1.55  tff(c_1057, plain, (![A_145]: (~v1_xboole_0(A_145) | A_145='#skF_3')), inference(resolution, [status(thm)], [c_1052, c_698])).
% 3.11/1.55  tff(c_1063, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_697, c_1057])).
% 3.11/1.55  tff(c_1069, plain, $false, inference(negUnitSimplification, [status(thm)], [c_984, c_1063])).
% 3.11/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.55  
% 3.11/1.55  Inference rules
% 3.11/1.55  ----------------------
% 3.11/1.55  #Ref     : 0
% 3.11/1.55  #Sup     : 208
% 3.11/1.55  #Fact    : 0
% 3.11/1.55  #Define  : 0
% 3.11/1.55  #Split   : 10
% 3.11/1.55  #Chain   : 0
% 3.11/1.55  #Close   : 0
% 3.11/1.55  
% 3.11/1.55  Ordering : KBO
% 3.11/1.55  
% 3.11/1.55  Simplification rules
% 3.11/1.55  ----------------------
% 3.11/1.55  #Subsume      : 27
% 3.11/1.55  #Demod        : 160
% 3.11/1.55  #Tautology    : 93
% 3.11/1.55  #SimpNegUnit  : 8
% 3.11/1.55  #BackRed      : 80
% 3.11/1.55  
% 3.11/1.55  #Partial instantiations: 0
% 3.11/1.55  #Strategies tried      : 1
% 3.11/1.55  
% 3.11/1.55  Timing (in seconds)
% 3.11/1.55  ----------------------
% 3.11/1.55  Preprocessing        : 0.34
% 3.11/1.55  Parsing              : 0.19
% 3.11/1.55  CNF conversion       : 0.02
% 3.11/1.55  Main loop            : 0.39
% 3.11/1.55  Inferencing          : 0.14
% 3.11/1.55  Reduction            : 0.13
% 3.11/1.55  Demodulation         : 0.09
% 3.11/1.55  BG Simplification    : 0.02
% 3.11/1.55  Subsumption          : 0.06
% 3.11/1.55  Abstraction          : 0.02
% 3.11/1.55  MUC search           : 0.00
% 3.11/1.55  Cooper               : 0.00
% 3.11/1.55  Total                : 0.77
% 3.11/1.55  Index Insertion      : 0.00
% 3.11/1.55  Index Deletion       : 0.00
% 3.11/1.55  Index Matching       : 0.00
% 3.11/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
