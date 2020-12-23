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
% DateTime   : Thu Dec  3 09:58:04 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 480 expanded)
%              Number of leaves         :   33 ( 167 expanded)
%              Depth                    :   14
%              Number of atoms          :  175 ( 968 expanded)
%              Number of equality atoms :   58 ( 215 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_101,negated_conjecture,(
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

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_49,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

tff(c_34,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,k1_zfmisc_1(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_106,plain,(
    ! [C_47,B_48,A_49] :
      ( ~ v1_xboole_0(C_47)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(C_47))
      | ~ r2_hidden(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_128,plain,(
    ! [B_51,A_52,A_53] :
      ( ~ v1_xboole_0(B_51)
      | ~ r2_hidden(A_52,A_53)
      | ~ r1_tarski(A_53,B_51) ) ),
    inference(resolution,[status(thm)],[c_24,c_106])).

tff(c_167,plain,(
    ! [B_59,A_60] :
      ( ~ v1_xboole_0(B_59)
      | ~ r1_tarski(A_60,B_59)
      | k1_xboole_0 = A_60 ) ),
    inference(resolution,[status(thm)],[c_2,c_128])).

tff(c_188,plain,
    ( ~ v1_xboole_0('#skF_4')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_34,c_167])).

tff(c_189,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_188])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_213,plain,(
    ! [A_65,C_66,B_67] :
      ( m1_subset_1(A_65,C_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(C_66))
      | ~ r2_hidden(A_65,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_226,plain,(
    ! [A_68] :
      ( m1_subset_1(A_68,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_68,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_213])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | ~ m1_subset_1(A_18,k1_zfmisc_1(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_237,plain,(
    ! [A_69] :
      ( r1_tarski(A_69,'#skF_2')
      | ~ r2_hidden(A_69,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_226,c_22])).

tff(c_242,plain,
    ( r1_tarski('#skF_1'('#skF_3'),'#skF_2')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2,c_237])).

tff(c_243,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_242])).

tff(c_344,plain,(
    ! [A_81] :
      ( r2_hidden('#skF_1'(A_81),A_81)
      | A_81 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_2])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_244,plain,(
    ! [A_70] :
      ( m1_subset_1(A_70,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_70,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_213])).

tff(c_254,plain,(
    ! [A_70] :
      ( r1_tarski(A_70,'#skF_2')
      | ~ r2_hidden(A_70,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_244,c_22])).

tff(c_355,plain,
    ( r1_tarski('#skF_1'('#skF_4'),'#skF_2')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_344,c_254])).

tff(c_402,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_355])).

tff(c_12,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_64,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_76,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(resolution,[status(thm)],[c_12,c_64])).

tff(c_53,plain,(
    ! [A_34,B_35] : k4_xboole_0(A_34,k2_xboole_0(A_34,B_35)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_xboole_0(k4_xboole_0(A_7,B_8),B_8) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_58,plain,(
    ! [A_34,B_35] : r1_xboole_0(k1_xboole_0,k2_xboole_0(A_34,B_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_8])).

tff(c_95,plain,(
    ! [B_45,A_46] :
      ( ~ r1_xboole_0(B_45,A_46)
      | ~ r1_tarski(B_45,A_46)
      | v1_xboole_0(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_98,plain,(
    ! [A_34,B_35] :
      ( ~ r1_tarski(k1_xboole_0,k2_xboole_0(A_34,B_35))
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_58,c_95])).

tff(c_104,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_98])).

tff(c_259,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_104])).

tff(c_412,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_259])).

tff(c_415,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_412])).

tff(c_417,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_355])).

tff(c_132,plain,(
    ! [A_54,B_55] :
      ( k6_setfam_1(A_54,B_55) = k1_setfam_1(B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(k1_zfmisc_1(A_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_149,plain,(
    k6_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_132])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( k8_setfam_1(A_12,B_13) = k6_setfam_1(A_12,B_13)
      | k1_xboole_0 = B_13
      | ~ m1_subset_1(B_13,k1_zfmisc_1(k1_zfmisc_1(A_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_379,plain,(
    ! [A_84,B_85] :
      ( k8_setfam_1(A_84,B_85) = k6_setfam_1(A_84,B_85)
      | B_85 = '#skF_3'
      | ~ m1_subset_1(B_85,k1_zfmisc_1(k1_zfmisc_1(A_84))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_16])).

tff(c_394,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k6_setfam_1('#skF_2','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_379])).

tff(c_401,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_394])).

tff(c_418,plain,(
    k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_417,c_401])).

tff(c_14,plain,(
    ! [A_12] :
      ( k8_setfam_1(A_12,k1_xboole_0) = A_12
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_40,plain,(
    ! [A_12] : k8_setfam_1(A_12,k1_xboole_0) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14])).

tff(c_264,plain,(
    ! [A_12] : k8_setfam_1(A_12,'#skF_3') = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_40])).

tff(c_32,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),k8_setfam_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_279,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_32])).

tff(c_419,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_279])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(k8_setfam_1(A_14,B_15),k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(k1_zfmisc_1(A_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_423,plain,
    ( m1_subset_1(k1_setfam_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_18])).

tff(c_427,plain,(
    m1_subset_1(k1_setfam_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_423])).

tff(c_435,plain,(
    r1_tarski(k1_setfam_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_427,c_22])).

tff(c_441,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_419,c_435])).

tff(c_443,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_242])).

tff(c_30,plain,(
    ! [B_27,A_26] :
      ( r1_tarski(k1_setfam_1(B_27),k1_setfam_1(A_26))
      | k1_xboole_0 = A_26
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_501,plain,(
    ! [A_91] :
      ( m1_subset_1(A_91,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_91,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_213])).

tff(c_518,plain,(
    ! [A_94] :
      ( r1_tarski(A_94,'#skF_2')
      | ~ r2_hidden(A_94,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_501,c_22])).

tff(c_523,plain,
    ( r1_tarski('#skF_1'('#skF_4'),'#skF_2')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2,c_518])).

tff(c_611,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_523])).

tff(c_620,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_611,c_104])).

tff(c_628,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_620])).

tff(c_630,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_523])).

tff(c_529,plain,(
    ! [A_97,B_98] :
      ( k8_setfam_1(A_97,B_98) = k6_setfam_1(A_97,B_98)
      | k1_xboole_0 = B_98
      | ~ m1_subset_1(B_98,k1_zfmisc_1(k1_zfmisc_1(A_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_547,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k6_setfam_1('#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_529])).

tff(c_559,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_547])).

tff(c_635,plain,(
    k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_630,c_559])).

tff(c_148,plain,(
    k6_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_132])).

tff(c_544,plain,
    ( k8_setfam_1('#skF_2','#skF_3') = k6_setfam_1('#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_38,c_529])).

tff(c_556,plain,
    ( k8_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_544])).

tff(c_557,plain,(
    k8_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_443,c_556])).

tff(c_563,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),k1_setfam_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_557,c_32])).

tff(c_636,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_4'),k1_setfam_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_635,c_563])).

tff(c_648,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_636])).

tff(c_651,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_648])).

tff(c_653,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_443,c_651])).

tff(c_654,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_666,plain,(
    ! [A_11] : m1_subset_1('#skF_3',k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_654,c_12])).

tff(c_665,plain,(
    ! [A_12] : k8_setfam_1(A_12,'#skF_3') = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_654,c_40])).

tff(c_713,plain,(
    ! [A_107,B_108] :
      ( m1_subset_1(k8_setfam_1(A_107,B_108),k1_zfmisc_1(A_107))
      | ~ m1_subset_1(B_108,k1_zfmisc_1(k1_zfmisc_1(A_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_727,plain,(
    ! [A_12] :
      ( m1_subset_1(A_12,k1_zfmisc_1(A_12))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(A_12))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_665,c_713])).

tff(c_734,plain,(
    ! [A_109] : m1_subset_1(A_109,k1_zfmisc_1(A_109)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_666,c_727])).

tff(c_749,plain,(
    ! [A_109] : r1_tarski(A_109,A_109) ),
    inference(resolution,[status(thm)],[c_734,c_22])).

tff(c_655,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_768,plain,(
    ! [A_116] :
      ( r2_hidden('#skF_1'(A_116),A_116)
      | A_116 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_654,c_2])).

tff(c_28,plain,(
    ! [C_25,B_24,A_23] :
      ( ~ v1_xboole_0(C_25)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(C_25))
      | ~ r2_hidden(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_748,plain,(
    ! [A_109,A_23] :
      ( ~ v1_xboole_0(A_109)
      | ~ r2_hidden(A_23,A_109) ) ),
    inference(resolution,[status(thm)],[c_734,c_28])).

tff(c_811,plain,(
    ! [A_119] :
      ( ~ v1_xboole_0(A_119)
      | A_119 = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_768,c_748])).

tff(c_820,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_655,c_811])).

tff(c_826,plain,(
    ! [A_12] : k8_setfam_1(A_12,'#skF_4') = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_820,c_665])).

tff(c_703,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_665,c_32])).

tff(c_861,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_826,c_703])).

tff(c_864,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_749,c_861])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:40:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.42  
% 2.71/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.42  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.71/1.42  
% 2.71/1.42  %Foreground sorts:
% 2.71/1.42  
% 2.71/1.42  
% 2.71/1.42  %Background operators:
% 2.71/1.42  
% 2.71/1.42  
% 2.71/1.42  %Foreground operators:
% 2.71/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.71/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.71/1.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.71/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.71/1.42  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.71/1.42  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.71/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.71/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.71/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.71/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.71/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.71/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.71/1.42  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.71/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.71/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.71/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.71/1.42  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.71/1.42  
% 3.01/1.45  tff(f_101, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_setfam_1)).
% 3.01/1.45  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.01/1.45  tff(f_72, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.01/1.45  tff(f_85, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.01/1.45  tff(f_78, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.01/1.45  tff(f_49, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.01/1.45  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.01/1.45  tff(f_45, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.01/1.45  tff(f_43, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.01/1.45  tff(f_68, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 3.01/1.45  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 3.01/1.45  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 3.01/1.45  tff(f_91, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 3.01/1.45  tff(c_34, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.01/1.45  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.01/1.45  tff(c_24, plain, (![A_18, B_19]: (m1_subset_1(A_18, k1_zfmisc_1(B_19)) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.01/1.45  tff(c_106, plain, (![C_47, B_48, A_49]: (~v1_xboole_0(C_47) | ~m1_subset_1(B_48, k1_zfmisc_1(C_47)) | ~r2_hidden(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.01/1.45  tff(c_128, plain, (![B_51, A_52, A_53]: (~v1_xboole_0(B_51) | ~r2_hidden(A_52, A_53) | ~r1_tarski(A_53, B_51))), inference(resolution, [status(thm)], [c_24, c_106])).
% 3.01/1.45  tff(c_167, plain, (![B_59, A_60]: (~v1_xboole_0(B_59) | ~r1_tarski(A_60, B_59) | k1_xboole_0=A_60)), inference(resolution, [status(thm)], [c_2, c_128])).
% 3.01/1.45  tff(c_188, plain, (~v1_xboole_0('#skF_4') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_34, c_167])).
% 3.01/1.45  tff(c_189, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_188])).
% 3.01/1.45  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.01/1.45  tff(c_213, plain, (![A_65, C_66, B_67]: (m1_subset_1(A_65, C_66) | ~m1_subset_1(B_67, k1_zfmisc_1(C_66)) | ~r2_hidden(A_65, B_67))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.01/1.45  tff(c_226, plain, (![A_68]: (m1_subset_1(A_68, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_68, '#skF_3'))), inference(resolution, [status(thm)], [c_38, c_213])).
% 3.01/1.45  tff(c_22, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | ~m1_subset_1(A_18, k1_zfmisc_1(B_19)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.01/1.45  tff(c_237, plain, (![A_69]: (r1_tarski(A_69, '#skF_2') | ~r2_hidden(A_69, '#skF_3'))), inference(resolution, [status(thm)], [c_226, c_22])).
% 3.01/1.45  tff(c_242, plain, (r1_tarski('#skF_1'('#skF_3'), '#skF_2') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2, c_237])).
% 3.01/1.45  tff(c_243, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_242])).
% 3.01/1.45  tff(c_344, plain, (![A_81]: (r2_hidden('#skF_1'(A_81), A_81) | A_81='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_243, c_2])).
% 3.01/1.45  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.01/1.45  tff(c_244, plain, (![A_70]: (m1_subset_1(A_70, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_70, '#skF_4'))), inference(resolution, [status(thm)], [c_36, c_213])).
% 3.01/1.45  tff(c_254, plain, (![A_70]: (r1_tarski(A_70, '#skF_2') | ~r2_hidden(A_70, '#skF_4'))), inference(resolution, [status(thm)], [c_244, c_22])).
% 3.01/1.45  tff(c_355, plain, (r1_tarski('#skF_1'('#skF_4'), '#skF_2') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_344, c_254])).
% 3.01/1.45  tff(c_402, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_355])).
% 3.01/1.45  tff(c_12, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.01/1.45  tff(c_64, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | ~m1_subset_1(A_38, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.01/1.45  tff(c_76, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(resolution, [status(thm)], [c_12, c_64])).
% 3.01/1.45  tff(c_53, plain, (![A_34, B_35]: (k4_xboole_0(A_34, k2_xboole_0(A_34, B_35))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.01/1.45  tff(c_8, plain, (![A_7, B_8]: (r1_xboole_0(k4_xboole_0(A_7, B_8), B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.01/1.45  tff(c_58, plain, (![A_34, B_35]: (r1_xboole_0(k1_xboole_0, k2_xboole_0(A_34, B_35)))), inference(superposition, [status(thm), theory('equality')], [c_53, c_8])).
% 3.01/1.45  tff(c_95, plain, (![B_45, A_46]: (~r1_xboole_0(B_45, A_46) | ~r1_tarski(B_45, A_46) | v1_xboole_0(B_45))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.01/1.45  tff(c_98, plain, (![A_34, B_35]: (~r1_tarski(k1_xboole_0, k2_xboole_0(A_34, B_35)) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_58, c_95])).
% 3.01/1.45  tff(c_104, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_76, c_98])).
% 3.01/1.45  tff(c_259, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_243, c_104])).
% 3.01/1.45  tff(c_412, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_402, c_259])).
% 3.01/1.45  tff(c_415, plain, $false, inference(negUnitSimplification, [status(thm)], [c_189, c_412])).
% 3.01/1.45  tff(c_417, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_355])).
% 3.01/1.45  tff(c_132, plain, (![A_54, B_55]: (k6_setfam_1(A_54, B_55)=k1_setfam_1(B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(k1_zfmisc_1(A_54))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.01/1.45  tff(c_149, plain, (k6_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_132])).
% 3.01/1.45  tff(c_16, plain, (![A_12, B_13]: (k8_setfam_1(A_12, B_13)=k6_setfam_1(A_12, B_13) | k1_xboole_0=B_13 | ~m1_subset_1(B_13, k1_zfmisc_1(k1_zfmisc_1(A_12))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.01/1.45  tff(c_379, plain, (![A_84, B_85]: (k8_setfam_1(A_84, B_85)=k6_setfam_1(A_84, B_85) | B_85='#skF_3' | ~m1_subset_1(B_85, k1_zfmisc_1(k1_zfmisc_1(A_84))))), inference(demodulation, [status(thm), theory('equality')], [c_243, c_16])).
% 3.01/1.45  tff(c_394, plain, (k8_setfam_1('#skF_2', '#skF_4')=k6_setfam_1('#skF_2', '#skF_4') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_36, c_379])).
% 3.01/1.45  tff(c_401, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_149, c_394])).
% 3.01/1.45  tff(c_418, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_417, c_401])).
% 3.01/1.45  tff(c_14, plain, (![A_12]: (k8_setfam_1(A_12, k1_xboole_0)=A_12 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_12))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.01/1.45  tff(c_40, plain, (![A_12]: (k8_setfam_1(A_12, k1_xboole_0)=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14])).
% 3.01/1.45  tff(c_264, plain, (![A_12]: (k8_setfam_1(A_12, '#skF_3')=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_243, c_40])).
% 3.01/1.45  tff(c_32, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), k8_setfam_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.01/1.45  tff(c_279, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_264, c_32])).
% 3.01/1.45  tff(c_419, plain, (~r1_tarski(k1_setfam_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_418, c_279])).
% 3.01/1.45  tff(c_18, plain, (![A_14, B_15]: (m1_subset_1(k8_setfam_1(A_14, B_15), k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(k1_zfmisc_1(A_14))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.01/1.45  tff(c_423, plain, (m1_subset_1(k1_setfam_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_418, c_18])).
% 3.01/1.45  tff(c_427, plain, (m1_subset_1(k1_setfam_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_423])).
% 3.01/1.45  tff(c_435, plain, (r1_tarski(k1_setfam_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_427, c_22])).
% 3.01/1.45  tff(c_441, plain, $false, inference(negUnitSimplification, [status(thm)], [c_419, c_435])).
% 3.01/1.45  tff(c_443, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_242])).
% 3.01/1.45  tff(c_30, plain, (![B_27, A_26]: (r1_tarski(k1_setfam_1(B_27), k1_setfam_1(A_26)) | k1_xboole_0=A_26 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.01/1.45  tff(c_501, plain, (![A_91]: (m1_subset_1(A_91, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_91, '#skF_4'))), inference(resolution, [status(thm)], [c_36, c_213])).
% 3.01/1.45  tff(c_518, plain, (![A_94]: (r1_tarski(A_94, '#skF_2') | ~r2_hidden(A_94, '#skF_4'))), inference(resolution, [status(thm)], [c_501, c_22])).
% 3.01/1.45  tff(c_523, plain, (r1_tarski('#skF_1'('#skF_4'), '#skF_2') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_2, c_518])).
% 3.01/1.45  tff(c_611, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_523])).
% 3.01/1.45  tff(c_620, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_611, c_104])).
% 3.01/1.45  tff(c_628, plain, $false, inference(negUnitSimplification, [status(thm)], [c_189, c_620])).
% 3.01/1.45  tff(c_630, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_523])).
% 3.01/1.45  tff(c_529, plain, (![A_97, B_98]: (k8_setfam_1(A_97, B_98)=k6_setfam_1(A_97, B_98) | k1_xboole_0=B_98 | ~m1_subset_1(B_98, k1_zfmisc_1(k1_zfmisc_1(A_97))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.01/1.45  tff(c_547, plain, (k8_setfam_1('#skF_2', '#skF_4')=k6_setfam_1('#skF_2', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_36, c_529])).
% 3.01/1.45  tff(c_559, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_149, c_547])).
% 3.01/1.45  tff(c_635, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_630, c_559])).
% 3.01/1.45  tff(c_148, plain, (k6_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_132])).
% 3.01/1.45  tff(c_544, plain, (k8_setfam_1('#skF_2', '#skF_3')=k6_setfam_1('#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_38, c_529])).
% 3.01/1.45  tff(c_556, plain, (k8_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_148, c_544])).
% 3.01/1.45  tff(c_557, plain, (k8_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_443, c_556])).
% 3.01/1.45  tff(c_563, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), k1_setfam_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_557, c_32])).
% 3.01/1.45  tff(c_636, plain, (~r1_tarski(k1_setfam_1('#skF_4'), k1_setfam_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_635, c_563])).
% 3.01/1.45  tff(c_648, plain, (k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_636])).
% 3.01/1.45  tff(c_651, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_648])).
% 3.01/1.45  tff(c_653, plain, $false, inference(negUnitSimplification, [status(thm)], [c_443, c_651])).
% 3.01/1.45  tff(c_654, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_188])).
% 3.01/1.45  tff(c_666, plain, (![A_11]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_654, c_12])).
% 3.01/1.45  tff(c_665, plain, (![A_12]: (k8_setfam_1(A_12, '#skF_3')=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_654, c_40])).
% 3.01/1.45  tff(c_713, plain, (![A_107, B_108]: (m1_subset_1(k8_setfam_1(A_107, B_108), k1_zfmisc_1(A_107)) | ~m1_subset_1(B_108, k1_zfmisc_1(k1_zfmisc_1(A_107))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.01/1.45  tff(c_727, plain, (![A_12]: (m1_subset_1(A_12, k1_zfmisc_1(A_12)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(A_12))))), inference(superposition, [status(thm), theory('equality')], [c_665, c_713])).
% 3.01/1.45  tff(c_734, plain, (![A_109]: (m1_subset_1(A_109, k1_zfmisc_1(A_109)))), inference(demodulation, [status(thm), theory('equality')], [c_666, c_727])).
% 3.01/1.45  tff(c_749, plain, (![A_109]: (r1_tarski(A_109, A_109))), inference(resolution, [status(thm)], [c_734, c_22])).
% 3.01/1.45  tff(c_655, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_188])).
% 3.01/1.45  tff(c_768, plain, (![A_116]: (r2_hidden('#skF_1'(A_116), A_116) | A_116='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_654, c_2])).
% 3.01/1.45  tff(c_28, plain, (![C_25, B_24, A_23]: (~v1_xboole_0(C_25) | ~m1_subset_1(B_24, k1_zfmisc_1(C_25)) | ~r2_hidden(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.01/1.45  tff(c_748, plain, (![A_109, A_23]: (~v1_xboole_0(A_109) | ~r2_hidden(A_23, A_109))), inference(resolution, [status(thm)], [c_734, c_28])).
% 3.01/1.45  tff(c_811, plain, (![A_119]: (~v1_xboole_0(A_119) | A_119='#skF_3')), inference(resolution, [status(thm)], [c_768, c_748])).
% 3.01/1.45  tff(c_820, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_655, c_811])).
% 3.01/1.45  tff(c_826, plain, (![A_12]: (k8_setfam_1(A_12, '#skF_4')=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_820, c_665])).
% 3.01/1.45  tff(c_703, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_665, c_32])).
% 3.01/1.45  tff(c_861, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_826, c_703])).
% 3.01/1.45  tff(c_864, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_749, c_861])).
% 3.01/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.45  
% 3.01/1.45  Inference rules
% 3.01/1.45  ----------------------
% 3.01/1.45  #Ref     : 0
% 3.01/1.45  #Sup     : 168
% 3.01/1.45  #Fact    : 0
% 3.01/1.45  #Define  : 0
% 3.01/1.45  #Split   : 7
% 3.01/1.45  #Chain   : 0
% 3.01/1.45  #Close   : 0
% 3.01/1.45  
% 3.01/1.45  Ordering : KBO
% 3.01/1.45  
% 3.01/1.45  Simplification rules
% 3.01/1.45  ----------------------
% 3.01/1.45  #Subsume      : 16
% 3.01/1.45  #Demod        : 120
% 3.01/1.45  #Tautology    : 70
% 3.01/1.45  #SimpNegUnit  : 7
% 3.01/1.45  #BackRed      : 65
% 3.01/1.45  
% 3.01/1.45  #Partial instantiations: 0
% 3.01/1.45  #Strategies tried      : 1
% 3.01/1.45  
% 3.01/1.45  Timing (in seconds)
% 3.01/1.45  ----------------------
% 3.01/1.45  Preprocessing        : 0.31
% 3.01/1.45  Parsing              : 0.16
% 3.01/1.45  CNF conversion       : 0.02
% 3.01/1.45  Main loop            : 0.36
% 3.01/1.45  Inferencing          : 0.13
% 3.01/1.45  Reduction            : 0.11
% 3.01/1.45  Demodulation         : 0.08
% 3.01/1.45  BG Simplification    : 0.02
% 3.01/1.45  Subsumption          : 0.05
% 3.01/1.45  Abstraction          : 0.02
% 3.01/1.45  MUC search           : 0.00
% 3.01/1.45  Cooper               : 0.00
% 3.01/1.45  Total                : 0.71
% 3.01/1.45  Index Insertion      : 0.00
% 3.01/1.45  Index Deletion       : 0.00
% 3.01/1.45  Index Matching       : 0.00
% 3.01/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
