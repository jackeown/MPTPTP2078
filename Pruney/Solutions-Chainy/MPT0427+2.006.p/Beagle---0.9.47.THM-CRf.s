%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:57 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 534 expanded)
%              Number of leaves         :   29 ( 181 expanded)
%              Depth                    :   13
%              Number of atoms          :  134 (1092 expanded)
%              Number of equality atoms :   48 ( 283 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_36,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_30,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,k1_zfmisc_1(B_21))
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_114,plain,(
    ! [B_41,A_42] :
      ( v1_xboole_0(B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42))
      | ~ v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_128,plain,(
    ! [A_43,B_44] :
      ( v1_xboole_0(A_43)
      | ~ v1_xboole_0(B_44)
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(resolution,[status(thm)],[c_30,c_114])).

tff(c_145,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_128])).

tff(c_146,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_145])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_169,plain,(
    ! [A_49,B_50] :
      ( k6_setfam_1(A_49,B_50) = k1_setfam_1(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(k1_zfmisc_1(A_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_181,plain,(
    k6_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_169])).

tff(c_231,plain,(
    ! [A_56,B_57] :
      ( k8_setfam_1(A_56,B_57) = k6_setfam_1(A_56,B_57)
      | k1_xboole_0 = B_57
      | ~ m1_subset_1(B_57,k1_zfmisc_1(k1_zfmisc_1(A_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_242,plain,
    ( k8_setfam_1('#skF_2','#skF_3') = k6_setfam_1('#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_40,c_231])).

tff(c_249,plain,
    ( k8_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_242])).

tff(c_252,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_249])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_182,plain,(
    k6_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_169])).

tff(c_245,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k6_setfam_1('#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_231])).

tff(c_251,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_245])).

tff(c_268,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_251])).

tff(c_269,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_268])).

tff(c_74,plain,(
    ! [A_34] :
      ( v1_xboole_0(A_34)
      | r2_hidden('#skF_1'(A_34),A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_65,plain,(
    ! [A_29,B_30] : ~ r2_hidden(A_29,k2_zfmisc_1(A_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_68,plain,(
    ! [A_7] : ~ r2_hidden(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_65])).

tff(c_83,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_74,c_68])).

tff(c_258,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_83])).

tff(c_270,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_258])).

tff(c_278,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_270])).

tff(c_279,plain,(
    k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_268])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_147,plain,(
    ! [A_45] :
      ( k8_setfam_1(A_45,k1_xboole_0) = A_45
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_150,plain,(
    ! [A_45] :
      ( k8_setfam_1(A_45,k1_xboole_0) = A_45
      | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(A_45)) ) ),
    inference(resolution,[status(thm)],[c_30,c_147])).

tff(c_153,plain,(
    ! [A_45] : k8_setfam_1(A_45,k1_xboole_0) = A_45 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_150])).

tff(c_256,plain,(
    ! [A_45] : k8_setfam_1(A_45,'#skF_3') = A_45 ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_153])).

tff(c_34,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),k8_setfam_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_307,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_34])).

tff(c_348,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_307])).

tff(c_24,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k8_setfam_1(A_16,B_17),k1_zfmisc_1(A_16))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k1_zfmisc_1(A_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_352,plain,
    ( m1_subset_1(k1_setfam_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_24])).

tff(c_356,plain,(
    m1_subset_1(k1_setfam_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_352])).

tff(c_28,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,B_21)
      | ~ m1_subset_1(A_20,k1_zfmisc_1(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_372,plain,(
    r1_tarski(k1_setfam_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_356,c_28])).

tff(c_377,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_348,c_372])).

tff(c_379,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_32,plain,(
    ! [B_23,A_22] :
      ( r1_tarski(k1_setfam_1(B_23),k1_setfam_1(A_22))
      | k1_xboole_0 = A_22
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_403,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_251])).

tff(c_410,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_83])).

tff(c_417,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_410])).

tff(c_418,plain,(
    k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_251])).

tff(c_378,plain,(
    k8_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_380,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),k1_setfam_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_34])).

tff(c_420,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_4'),k1_setfam_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_380])).

tff(c_432,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_420])).

tff(c_435,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_432])).

tff(c_437,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_379,c_435])).

tff(c_439,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_447,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_439,c_6])).

tff(c_438,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_443,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_438,c_6])).

tff(c_460,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_447,c_443])).

tff(c_454,plain,(
    ! [A_6] : r1_tarski('#skF_3',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_8])).

tff(c_485,plain,(
    ! [A_6] : r1_tarski('#skF_4',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_454])).

tff(c_20,plain,(
    ! [A_14] :
      ( k8_setfam_1(A_14,k1_xboole_0) = A_14
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_495,plain,(
    ! [A_67] :
      ( k8_setfam_1(A_67,'#skF_4') = A_67
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(A_67))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_447,c_447,c_20])).

tff(c_498,plain,(
    ! [A_67] :
      ( k8_setfam_1(A_67,'#skF_4') = A_67
      | ~ r1_tarski('#skF_4',k1_zfmisc_1(A_67)) ) ),
    inference(resolution,[status(thm)],[c_30,c_495])).

tff(c_504,plain,(
    ! [A_67] : k8_setfam_1(A_67,'#skF_4') = A_67 ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_498])).

tff(c_605,plain,(
    ! [A_81,B_82] :
      ( m1_subset_1(k8_setfam_1(A_81,B_82),k1_zfmisc_1(A_81))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(k1_zfmisc_1(A_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_640,plain,(
    ! [A_85] :
      ( m1_subset_1(A_85,k1_zfmisc_1(A_85))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(A_85))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_504,c_605])).

tff(c_643,plain,(
    ! [A_85] :
      ( m1_subset_1(A_85,k1_zfmisc_1(A_85))
      | ~ r1_tarski('#skF_4',k1_zfmisc_1(A_85)) ) ),
    inference(resolution,[status(thm)],[c_30,c_640])).

tff(c_651,plain,(
    ! [A_86] : m1_subset_1(A_86,k1_zfmisc_1(A_86)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_643])).

tff(c_669,plain,(
    ! [A_86] : r1_tarski(A_86,A_86) ),
    inference(resolution,[status(thm)],[c_651,c_28])).

tff(c_467,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),k8_setfam_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_34])).

tff(c_558,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_504,c_467])).

tff(c_672,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_669,c_558])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:17:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.37  
% 2.59/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.37  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.59/1.37  
% 2.59/1.37  %Foreground sorts:
% 2.59/1.37  
% 2.59/1.37  
% 2.59/1.37  %Background operators:
% 2.59/1.37  
% 2.59/1.37  
% 2.59/1.37  %Foreground operators:
% 2.59/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.59/1.37  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.59/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.59/1.37  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.59/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.59/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.59/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.59/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.59/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.59/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.59/1.37  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.59/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.59/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.59/1.37  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.59/1.37  
% 2.84/1.39  tff(f_92, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_setfam_1)).
% 2.84/1.39  tff(f_76, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.84/1.39  tff(f_53, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.84/1.39  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 2.84/1.39  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 2.84/1.39  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.84/1.39  tff(f_43, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.84/1.39  tff(f_46, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.84/1.39  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.84/1.39  tff(f_68, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 2.84/1.39  tff(f_82, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 2.84/1.39  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.84/1.39  tff(c_36, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.84/1.39  tff(c_30, plain, (![A_20, B_21]: (m1_subset_1(A_20, k1_zfmisc_1(B_21)) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.84/1.39  tff(c_114, plain, (![B_41, A_42]: (v1_xboole_0(B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)) | ~v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.84/1.39  tff(c_128, plain, (![A_43, B_44]: (v1_xboole_0(A_43) | ~v1_xboole_0(B_44) | ~r1_tarski(A_43, B_44))), inference(resolution, [status(thm)], [c_30, c_114])).
% 2.84/1.39  tff(c_145, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_128])).
% 2.84/1.39  tff(c_146, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_145])).
% 2.84/1.39  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.84/1.39  tff(c_169, plain, (![A_49, B_50]: (k6_setfam_1(A_49, B_50)=k1_setfam_1(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(k1_zfmisc_1(A_49))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.84/1.39  tff(c_181, plain, (k6_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_169])).
% 2.84/1.39  tff(c_231, plain, (![A_56, B_57]: (k8_setfam_1(A_56, B_57)=k6_setfam_1(A_56, B_57) | k1_xboole_0=B_57 | ~m1_subset_1(B_57, k1_zfmisc_1(k1_zfmisc_1(A_56))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.84/1.39  tff(c_242, plain, (k8_setfam_1('#skF_2', '#skF_3')=k6_setfam_1('#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_40, c_231])).
% 2.84/1.39  tff(c_249, plain, (k8_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_181, c_242])).
% 2.84/1.39  tff(c_252, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_249])).
% 2.84/1.39  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.84/1.39  tff(c_182, plain, (k6_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_169])).
% 2.84/1.39  tff(c_245, plain, (k8_setfam_1('#skF_2', '#skF_4')=k6_setfam_1('#skF_2', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_38, c_231])).
% 2.84/1.39  tff(c_251, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_182, c_245])).
% 2.84/1.39  tff(c_268, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_252, c_251])).
% 2.84/1.39  tff(c_269, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_268])).
% 2.84/1.39  tff(c_74, plain, (![A_34]: (v1_xboole_0(A_34) | r2_hidden('#skF_1'(A_34), A_34))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.84/1.39  tff(c_12, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.84/1.39  tff(c_65, plain, (![A_29, B_30]: (~r2_hidden(A_29, k2_zfmisc_1(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.84/1.39  tff(c_68, plain, (![A_7]: (~r2_hidden(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_65])).
% 2.84/1.39  tff(c_83, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_74, c_68])).
% 2.84/1.39  tff(c_258, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_252, c_83])).
% 2.84/1.39  tff(c_270, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_269, c_258])).
% 2.84/1.39  tff(c_278, plain, $false, inference(negUnitSimplification, [status(thm)], [c_146, c_270])).
% 2.84/1.39  tff(c_279, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4')), inference(splitRight, [status(thm)], [c_268])).
% 2.84/1.39  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.84/1.39  tff(c_147, plain, (![A_45]: (k8_setfam_1(A_45, k1_xboole_0)=A_45 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_45))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.84/1.39  tff(c_150, plain, (![A_45]: (k8_setfam_1(A_45, k1_xboole_0)=A_45 | ~r1_tarski(k1_xboole_0, k1_zfmisc_1(A_45)))), inference(resolution, [status(thm)], [c_30, c_147])).
% 2.84/1.39  tff(c_153, plain, (![A_45]: (k8_setfam_1(A_45, k1_xboole_0)=A_45)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_150])).
% 2.84/1.39  tff(c_256, plain, (![A_45]: (k8_setfam_1(A_45, '#skF_3')=A_45)), inference(demodulation, [status(thm), theory('equality')], [c_252, c_153])).
% 2.84/1.39  tff(c_34, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), k8_setfam_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.84/1.39  tff(c_307, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_256, c_34])).
% 2.84/1.39  tff(c_348, plain, (~r1_tarski(k1_setfam_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_279, c_307])).
% 2.84/1.39  tff(c_24, plain, (![A_16, B_17]: (m1_subset_1(k8_setfam_1(A_16, B_17), k1_zfmisc_1(A_16)) | ~m1_subset_1(B_17, k1_zfmisc_1(k1_zfmisc_1(A_16))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.84/1.39  tff(c_352, plain, (m1_subset_1(k1_setfam_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_279, c_24])).
% 2.84/1.39  tff(c_356, plain, (m1_subset_1(k1_setfam_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_352])).
% 2.84/1.39  tff(c_28, plain, (![A_20, B_21]: (r1_tarski(A_20, B_21) | ~m1_subset_1(A_20, k1_zfmisc_1(B_21)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.84/1.39  tff(c_372, plain, (r1_tarski(k1_setfam_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_356, c_28])).
% 2.84/1.39  tff(c_377, plain, $false, inference(negUnitSimplification, [status(thm)], [c_348, c_372])).
% 2.84/1.39  tff(c_379, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_249])).
% 2.84/1.39  tff(c_32, plain, (![B_23, A_22]: (r1_tarski(k1_setfam_1(B_23), k1_setfam_1(A_22)) | k1_xboole_0=A_22 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.84/1.39  tff(c_403, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_251])).
% 2.84/1.39  tff(c_410, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_403, c_83])).
% 2.84/1.39  tff(c_417, plain, $false, inference(negUnitSimplification, [status(thm)], [c_146, c_410])).
% 2.84/1.39  tff(c_418, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4')), inference(splitRight, [status(thm)], [c_251])).
% 2.84/1.39  tff(c_378, plain, (k8_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_249])).
% 2.84/1.39  tff(c_380, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), k1_setfam_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_378, c_34])).
% 2.84/1.39  tff(c_420, plain, (~r1_tarski(k1_setfam_1('#skF_4'), k1_setfam_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_418, c_380])).
% 2.84/1.39  tff(c_432, plain, (k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_420])).
% 2.84/1.39  tff(c_435, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_432])).
% 2.84/1.39  tff(c_437, plain, $false, inference(negUnitSimplification, [status(thm)], [c_379, c_435])).
% 2.84/1.39  tff(c_439, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_145])).
% 2.84/1.39  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.84/1.39  tff(c_447, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_439, c_6])).
% 2.84/1.39  tff(c_438, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_145])).
% 2.84/1.39  tff(c_443, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_438, c_6])).
% 2.84/1.39  tff(c_460, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_447, c_443])).
% 2.84/1.39  tff(c_454, plain, (![A_6]: (r1_tarski('#skF_3', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_443, c_8])).
% 2.84/1.39  tff(c_485, plain, (![A_6]: (r1_tarski('#skF_4', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_460, c_454])).
% 2.84/1.39  tff(c_20, plain, (![A_14]: (k8_setfam_1(A_14, k1_xboole_0)=A_14 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_14))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.84/1.39  tff(c_495, plain, (![A_67]: (k8_setfam_1(A_67, '#skF_4')=A_67 | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(A_67))))), inference(demodulation, [status(thm), theory('equality')], [c_447, c_447, c_20])).
% 2.84/1.39  tff(c_498, plain, (![A_67]: (k8_setfam_1(A_67, '#skF_4')=A_67 | ~r1_tarski('#skF_4', k1_zfmisc_1(A_67)))), inference(resolution, [status(thm)], [c_30, c_495])).
% 2.84/1.39  tff(c_504, plain, (![A_67]: (k8_setfam_1(A_67, '#skF_4')=A_67)), inference(demodulation, [status(thm), theory('equality')], [c_485, c_498])).
% 2.84/1.39  tff(c_605, plain, (![A_81, B_82]: (m1_subset_1(k8_setfam_1(A_81, B_82), k1_zfmisc_1(A_81)) | ~m1_subset_1(B_82, k1_zfmisc_1(k1_zfmisc_1(A_81))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.84/1.39  tff(c_640, plain, (![A_85]: (m1_subset_1(A_85, k1_zfmisc_1(A_85)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(A_85))))), inference(superposition, [status(thm), theory('equality')], [c_504, c_605])).
% 2.84/1.39  tff(c_643, plain, (![A_85]: (m1_subset_1(A_85, k1_zfmisc_1(A_85)) | ~r1_tarski('#skF_4', k1_zfmisc_1(A_85)))), inference(resolution, [status(thm)], [c_30, c_640])).
% 2.84/1.39  tff(c_651, plain, (![A_86]: (m1_subset_1(A_86, k1_zfmisc_1(A_86)))), inference(demodulation, [status(thm), theory('equality')], [c_485, c_643])).
% 2.84/1.39  tff(c_669, plain, (![A_86]: (r1_tarski(A_86, A_86))), inference(resolution, [status(thm)], [c_651, c_28])).
% 2.84/1.39  tff(c_467, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), k8_setfam_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_460, c_34])).
% 2.84/1.39  tff(c_558, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_504, c_504, c_467])).
% 2.84/1.39  tff(c_672, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_669, c_558])).
% 2.84/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.39  
% 2.84/1.39  Inference rules
% 2.84/1.39  ----------------------
% 2.84/1.39  #Ref     : 0
% 2.84/1.39  #Sup     : 129
% 2.84/1.39  #Fact    : 0
% 2.84/1.39  #Define  : 0
% 2.84/1.39  #Split   : 6
% 2.84/1.39  #Chain   : 0
% 2.84/1.39  #Close   : 0
% 2.84/1.39  
% 2.84/1.39  Ordering : KBO
% 2.84/1.39  
% 2.84/1.39  Simplification rules
% 2.84/1.39  ----------------------
% 2.84/1.39  #Subsume      : 9
% 2.84/1.39  #Demod        : 113
% 2.84/1.39  #Tautology    : 85
% 2.84/1.39  #SimpNegUnit  : 4
% 2.84/1.39  #BackRed      : 48
% 2.84/1.39  
% 2.84/1.39  #Partial instantiations: 0
% 2.84/1.39  #Strategies tried      : 1
% 2.84/1.39  
% 2.84/1.39  Timing (in seconds)
% 2.84/1.39  ----------------------
% 2.84/1.40  Preprocessing        : 0.32
% 2.84/1.40  Parsing              : 0.17
% 2.84/1.40  CNF conversion       : 0.02
% 2.84/1.40  Main loop            : 0.30
% 2.84/1.40  Inferencing          : 0.10
% 2.84/1.40  Reduction            : 0.10
% 2.84/1.40  Demodulation         : 0.07
% 2.84/1.40  BG Simplification    : 0.02
% 2.84/1.40  Subsumption          : 0.04
% 2.84/1.40  Abstraction          : 0.02
% 2.84/1.40  MUC search           : 0.00
% 2.84/1.40  Cooper               : 0.00
% 2.84/1.40  Total                : 0.66
% 2.84/1.40  Index Insertion      : 0.00
% 2.84/1.40  Index Deletion       : 0.00
% 2.84/1.40  Index Matching       : 0.00
% 2.84/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
