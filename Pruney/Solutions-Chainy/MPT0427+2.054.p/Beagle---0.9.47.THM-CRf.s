%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:03 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 330 expanded)
%              Number of leaves         :   21 ( 114 expanded)
%              Depth                    :   10
%              Number of atoms          :   94 ( 696 expanded)
%              Number of equality atoms :   41 ( 317 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_31,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_67,plain,(
    ! [A_24,B_25] :
      ( k6_setfam_1(A_24,B_25) = k1_setfam_1(B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(k1_zfmisc_1(A_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_79,plain,(
    k6_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_67])).

tff(c_125,plain,(
    ! [A_31,B_32] :
      ( k8_setfam_1(A_31,B_32) = k6_setfam_1(A_31,B_32)
      | k1_xboole_0 = B_32
      | ~ m1_subset_1(B_32,k1_zfmisc_1(k1_zfmisc_1(A_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_136,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k6_setfam_1('#skF_1','#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_26,c_125])).

tff(c_143,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_136])).

tff(c_146,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_143])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_80,plain,(
    k6_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_67])).

tff(c_139,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k6_setfam_1('#skF_1','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_24,c_125])).

tff(c_145,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_139])).

tff(c_194,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_145])).

tff(c_195,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_194])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_49,plain,(
    ! [A_20] :
      ( k8_setfam_1(A_20,k1_xboole_0) = A_20
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_52,plain,(
    ! [A_20] :
      ( k8_setfam_1(A_20,k1_xboole_0) = A_20
      | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(A_20)) ) ),
    inference(resolution,[status(thm)],[c_16,c_49])).

tff(c_55,plain,(
    ! [A_20] : k8_setfam_1(A_20,k1_xboole_0) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_52])).

tff(c_150,plain,(
    ! [A_20] : k8_setfam_1(A_20,'#skF_2') = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_55])).

tff(c_198,plain,(
    ! [A_20] : k8_setfam_1(A_20,'#skF_3') = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_150])).

tff(c_20,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_165,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_20])).

tff(c_218,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_165])).

tff(c_85,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(k8_setfam_1(A_26,B_27),k1_zfmisc_1(A_26))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(k1_zfmisc_1(A_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_238,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(k8_setfam_1(A_40,B_41),A_40)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(k1_zfmisc_1(A_40))) ) ),
    inference(resolution,[status(thm)],[c_85,c_14])).

tff(c_246,plain,(
    r1_tarski(k8_setfam_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_238])).

tff(c_250,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_246])).

tff(c_252,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_250])).

tff(c_253,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_255,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_165])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k8_setfam_1(A_5,B_6),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(k1_zfmisc_1(A_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_259,plain,
    ( m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_10])).

tff(c_263,plain,(
    m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_259])).

tff(c_267,plain,(
    r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_263,c_14])).

tff(c_271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_255,c_267])).

tff(c_273,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_143])).

tff(c_22,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_18,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_setfam_1(B_12),k1_setfam_1(A_11))
      | k1_xboole_0 = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_288,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_145])).

tff(c_289,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_273])).

tff(c_4,plain,(
    ! [A_2] :
      ( k1_xboole_0 = A_2
      | ~ r1_tarski(A_2,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_307,plain,(
    ! [A_43] :
      ( A_43 = '#skF_3'
      | ~ r1_tarski(A_43,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_288,c_4])).

tff(c_314,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_22,c_307])).

tff(c_320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_289,c_314])).

tff(c_321,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_272,plain,(
    k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_143])).

tff(c_274,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_20])).

tff(c_323,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_274])).

tff(c_335,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_323])).

tff(c_338,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_335])).

tff(c_340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_273,c_338])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:39:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.23  
% 1.97/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.23  %$ r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.11/1.23  
% 2.11/1.23  %Foreground sorts:
% 2.11/1.23  
% 2.11/1.23  
% 2.11/1.23  %Background operators:
% 2.11/1.23  
% 2.11/1.23  
% 2.11/1.23  %Foreground operators:
% 2.11/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.11/1.23  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.11/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.11/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.11/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.11/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.11/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.11/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.23  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.11/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.11/1.23  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.11/1.23  
% 2.13/1.25  tff(f_70, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_setfam_1)).
% 2.13/1.25  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 2.13/1.25  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 2.13/1.25  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.13/1.25  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.13/1.25  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 2.13/1.25  tff(f_60, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 2.13/1.25  tff(f_31, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.13/1.25  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.13/1.25  tff(c_67, plain, (![A_24, B_25]: (k6_setfam_1(A_24, B_25)=k1_setfam_1(B_25) | ~m1_subset_1(B_25, k1_zfmisc_1(k1_zfmisc_1(A_24))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.13/1.25  tff(c_79, plain, (k6_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(resolution, [status(thm)], [c_26, c_67])).
% 2.13/1.25  tff(c_125, plain, (![A_31, B_32]: (k8_setfam_1(A_31, B_32)=k6_setfam_1(A_31, B_32) | k1_xboole_0=B_32 | ~m1_subset_1(B_32, k1_zfmisc_1(k1_zfmisc_1(A_31))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.13/1.25  tff(c_136, plain, (k8_setfam_1('#skF_1', '#skF_2')=k6_setfam_1('#skF_1', '#skF_2') | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_26, c_125])).
% 2.13/1.25  tff(c_143, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_79, c_136])).
% 2.13/1.25  tff(c_146, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_143])).
% 2.13/1.25  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.13/1.25  tff(c_80, plain, (k6_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_67])).
% 2.13/1.25  tff(c_139, plain, (k8_setfam_1('#skF_1', '#skF_3')=k6_setfam_1('#skF_1', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_24, c_125])).
% 2.13/1.25  tff(c_145, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_139])).
% 2.13/1.25  tff(c_194, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_146, c_145])).
% 2.13/1.25  tff(c_195, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_194])).
% 2.13/1.25  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.13/1.25  tff(c_16, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.13/1.25  tff(c_49, plain, (![A_20]: (k8_setfam_1(A_20, k1_xboole_0)=A_20 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_20))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.13/1.25  tff(c_52, plain, (![A_20]: (k8_setfam_1(A_20, k1_xboole_0)=A_20 | ~r1_tarski(k1_xboole_0, k1_zfmisc_1(A_20)))), inference(resolution, [status(thm)], [c_16, c_49])).
% 2.13/1.25  tff(c_55, plain, (![A_20]: (k8_setfam_1(A_20, k1_xboole_0)=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_52])).
% 2.13/1.25  tff(c_150, plain, (![A_20]: (k8_setfam_1(A_20, '#skF_2')=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_146, c_55])).
% 2.13/1.25  tff(c_198, plain, (![A_20]: (k8_setfam_1(A_20, '#skF_3')=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_195, c_150])).
% 2.13/1.25  tff(c_20, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.13/1.25  tff(c_165, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_150, c_20])).
% 2.13/1.25  tff(c_218, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_198, c_165])).
% 2.13/1.25  tff(c_85, plain, (![A_26, B_27]: (m1_subset_1(k8_setfam_1(A_26, B_27), k1_zfmisc_1(A_26)) | ~m1_subset_1(B_27, k1_zfmisc_1(k1_zfmisc_1(A_26))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.13/1.25  tff(c_14, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~m1_subset_1(A_9, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.13/1.25  tff(c_238, plain, (![A_40, B_41]: (r1_tarski(k8_setfam_1(A_40, B_41), A_40) | ~m1_subset_1(B_41, k1_zfmisc_1(k1_zfmisc_1(A_40))))), inference(resolution, [status(thm)], [c_85, c_14])).
% 2.13/1.25  tff(c_246, plain, (r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_24, c_238])).
% 2.13/1.25  tff(c_250, plain, (r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_198, c_246])).
% 2.13/1.25  tff(c_252, plain, $false, inference(negUnitSimplification, [status(thm)], [c_218, c_250])).
% 2.13/1.25  tff(c_253, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_194])).
% 2.13/1.25  tff(c_255, plain, (~r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_253, c_165])).
% 2.13/1.25  tff(c_10, plain, (![A_5, B_6]: (m1_subset_1(k8_setfam_1(A_5, B_6), k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(k1_zfmisc_1(A_5))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.13/1.25  tff(c_259, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_253, c_10])).
% 2.13/1.25  tff(c_263, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_259])).
% 2.13/1.25  tff(c_267, plain, (r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_263, c_14])).
% 2.13/1.25  tff(c_271, plain, $false, inference(negUnitSimplification, [status(thm)], [c_255, c_267])).
% 2.13/1.25  tff(c_273, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_143])).
% 2.13/1.25  tff(c_22, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.13/1.25  tff(c_18, plain, (![B_12, A_11]: (r1_tarski(k1_setfam_1(B_12), k1_setfam_1(A_11)) | k1_xboole_0=A_11 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.13/1.25  tff(c_288, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_145])).
% 2.13/1.25  tff(c_289, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_288, c_273])).
% 2.13/1.25  tff(c_4, plain, (![A_2]: (k1_xboole_0=A_2 | ~r1_tarski(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.13/1.25  tff(c_307, plain, (![A_43]: (A_43='#skF_3' | ~r1_tarski(A_43, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_288, c_288, c_4])).
% 2.13/1.25  tff(c_314, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_22, c_307])).
% 2.13/1.25  tff(c_320, plain, $false, inference(negUnitSimplification, [status(thm)], [c_289, c_314])).
% 2.13/1.25  tff(c_321, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_145])).
% 2.13/1.25  tff(c_272, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(splitRight, [status(thm)], [c_143])).
% 2.13/1.25  tff(c_274, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_272, c_20])).
% 2.13/1.25  tff(c_323, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_321, c_274])).
% 2.13/1.25  tff(c_335, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_18, c_323])).
% 2.13/1.25  tff(c_338, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_335])).
% 2.13/1.25  tff(c_340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_273, c_338])).
% 2.13/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.25  
% 2.13/1.25  Inference rules
% 2.13/1.25  ----------------------
% 2.13/1.25  #Ref     : 0
% 2.13/1.25  #Sup     : 64
% 2.13/1.25  #Fact    : 0
% 2.13/1.25  #Define  : 0
% 2.13/1.25  #Split   : 3
% 2.13/1.25  #Chain   : 0
% 2.13/1.25  #Close   : 0
% 2.13/1.25  
% 2.13/1.25  Ordering : KBO
% 2.13/1.25  
% 2.13/1.25  Simplification rules
% 2.13/1.25  ----------------------
% 2.13/1.25  #Subsume      : 0
% 2.13/1.25  #Demod        : 49
% 2.13/1.25  #Tautology    : 43
% 2.13/1.25  #SimpNegUnit  : 4
% 2.13/1.25  #BackRed      : 24
% 2.13/1.25  
% 2.13/1.25  #Partial instantiations: 0
% 2.13/1.25  #Strategies tried      : 1
% 2.13/1.25  
% 2.13/1.25  Timing (in seconds)
% 2.13/1.25  ----------------------
% 2.13/1.25  Preprocessing        : 0.29
% 2.13/1.25  Parsing              : 0.15
% 2.13/1.25  CNF conversion       : 0.02
% 2.13/1.25  Main loop            : 0.21
% 2.13/1.25  Inferencing          : 0.08
% 2.13/1.25  Reduction            : 0.07
% 2.13/1.25  Demodulation         : 0.05
% 2.13/1.25  BG Simplification    : 0.01
% 2.13/1.25  Subsumption          : 0.03
% 2.13/1.25  Abstraction          : 0.01
% 2.13/1.25  MUC search           : 0.00
% 2.13/1.25  Cooper               : 0.00
% 2.13/1.25  Total                : 0.53
% 2.13/1.25  Index Insertion      : 0.00
% 2.13/1.25  Index Deletion       : 0.00
% 2.13/1.25  Index Matching       : 0.00
% 2.13/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
