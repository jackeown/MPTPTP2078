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
% DateTime   : Thu Dec  3 09:58:00 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 153 expanded)
%              Number of leaves         :   21 (  58 expanded)
%              Depth                    :    9
%              Number of atoms          :   86 ( 303 expanded)
%              Number of equality atoms :   35 ( 118 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_100,plain,(
    ! [A_26,B_27] :
      ( k6_setfam_1(A_26,B_27) = k1_setfam_1(B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(k1_zfmisc_1(A_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_113,plain,(
    k6_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_100])).

tff(c_183,plain,(
    ! [A_37,B_38] :
      ( k8_setfam_1(A_37,B_38) = k6_setfam_1(A_37,B_38)
      | k1_xboole_0 = B_38
      | ~ m1_subset_1(B_38,k1_zfmisc_1(k1_zfmisc_1(A_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_197,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k6_setfam_1('#skF_1','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_28,c_183])).

tff(c_203,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_197])).

tff(c_223,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_203])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_229,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_8])).

tff(c_26,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_48,plain,(
    ! [B_21,A_22] :
      ( B_21 = A_22
      | ~ r1_tarski(B_21,A_22)
      | ~ r1_tarski(A_22,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_48])).

tff(c_80,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_237,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_80])).

tff(c_238,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_203])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k8_setfam_1(A_6,B_7),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(k1_zfmisc_1(A_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_244,plain,
    ( m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_14])).

tff(c_248,plain,(
    m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_244])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_253,plain,(
    r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_248,c_18])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_112,plain,(
    k6_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_100])).

tff(c_194,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k6_setfam_1('#skF_1','#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_183])).

tff(c_201,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_194])).

tff(c_257,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_201])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_82,plain,(
    ! [A_24] :
      ( k8_setfam_1(A_24,k1_xboole_0) = A_24
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_85,plain,(
    ! [A_24] :
      ( k8_setfam_1(A_24,k1_xboole_0) = A_24
      | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(A_24)) ) ),
    inference(resolution,[status(thm)],[c_20,c_82])).

tff(c_88,plain,(
    ! [A_24] : k8_setfam_1(A_24,k1_xboole_0) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_85])).

tff(c_262,plain,(
    ! [A_24] : k8_setfam_1(A_24,'#skF_2') = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_88])).

tff(c_24,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_240,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k8_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_24])).

tff(c_280,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_240])).

tff(c_283,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_280])).

tff(c_285,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_201])).

tff(c_22,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k1_setfam_1(B_13),k1_setfam_1(A_12))
      | k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_284,plain,(
    k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_201])).

tff(c_286,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_240])).

tff(c_298,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_286])).

tff(c_301,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_298])).

tff(c_303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_285,c_301])).

tff(c_304,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_307,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_24])).

tff(c_313,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_307])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:30:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.29  
% 2.07/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.29  %$ r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.07/1.29  
% 2.07/1.29  %Foreground sorts:
% 2.07/1.29  
% 2.07/1.29  
% 2.07/1.29  %Background operators:
% 2.07/1.29  
% 2.07/1.29  
% 2.07/1.29  %Foreground operators:
% 2.07/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.07/1.29  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.07/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.07/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.07/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.07/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.29  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.07/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.07/1.29  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.07/1.29  
% 2.27/1.31  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.27/1.31  tff(f_72, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_setfam_1)).
% 2.27/1.31  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 2.27/1.31  tff(f_44, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 2.27/1.31  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.27/1.31  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 2.27/1.31  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.27/1.31  tff(f_62, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 2.27/1.31  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.27/1.31  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.27/1.31  tff(c_100, plain, (![A_26, B_27]: (k6_setfam_1(A_26, B_27)=k1_setfam_1(B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(k1_zfmisc_1(A_26))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.27/1.31  tff(c_113, plain, (k6_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_100])).
% 2.27/1.31  tff(c_183, plain, (![A_37, B_38]: (k8_setfam_1(A_37, B_38)=k6_setfam_1(A_37, B_38) | k1_xboole_0=B_38 | ~m1_subset_1(B_38, k1_zfmisc_1(k1_zfmisc_1(A_37))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.27/1.31  tff(c_197, plain, (k8_setfam_1('#skF_1', '#skF_3')=k6_setfam_1('#skF_1', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_28, c_183])).
% 2.27/1.31  tff(c_203, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_113, c_197])).
% 2.27/1.31  tff(c_223, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_203])).
% 2.27/1.31  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.27/1.31  tff(c_229, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_223, c_8])).
% 2.27/1.31  tff(c_26, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.27/1.31  tff(c_48, plain, (![B_21, A_22]: (B_21=A_22 | ~r1_tarski(B_21, A_22) | ~r1_tarski(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.27/1.31  tff(c_66, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_48])).
% 2.27/1.31  tff(c_80, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_66])).
% 2.27/1.31  tff(c_237, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_229, c_80])).
% 2.27/1.31  tff(c_238, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_203])).
% 2.27/1.31  tff(c_14, plain, (![A_6, B_7]: (m1_subset_1(k8_setfam_1(A_6, B_7), k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(k1_zfmisc_1(A_6))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.27/1.31  tff(c_244, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_238, c_14])).
% 2.27/1.31  tff(c_248, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_244])).
% 2.27/1.31  tff(c_18, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.27/1.31  tff(c_253, plain, (r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_248, c_18])).
% 2.27/1.31  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.27/1.31  tff(c_112, plain, (k6_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(resolution, [status(thm)], [c_30, c_100])).
% 2.27/1.31  tff(c_194, plain, (k8_setfam_1('#skF_1', '#skF_2')=k6_setfam_1('#skF_1', '#skF_2') | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_183])).
% 2.27/1.31  tff(c_201, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_194])).
% 2.27/1.31  tff(c_257, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_201])).
% 2.27/1.31  tff(c_20, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.27/1.31  tff(c_82, plain, (![A_24]: (k8_setfam_1(A_24, k1_xboole_0)=A_24 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_24))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.27/1.31  tff(c_85, plain, (![A_24]: (k8_setfam_1(A_24, k1_xboole_0)=A_24 | ~r1_tarski(k1_xboole_0, k1_zfmisc_1(A_24)))), inference(resolution, [status(thm)], [c_20, c_82])).
% 2.27/1.31  tff(c_88, plain, (![A_24]: (k8_setfam_1(A_24, k1_xboole_0)=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_85])).
% 2.27/1.31  tff(c_262, plain, (![A_24]: (k8_setfam_1(A_24, '#skF_2')=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_257, c_88])).
% 2.27/1.31  tff(c_24, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.27/1.31  tff(c_240, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_238, c_24])).
% 2.27/1.31  tff(c_280, plain, (~r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_262, c_240])).
% 2.27/1.31  tff(c_283, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_253, c_280])).
% 2.27/1.31  tff(c_285, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_201])).
% 2.27/1.31  tff(c_22, plain, (![B_13, A_12]: (r1_tarski(k1_setfam_1(B_13), k1_setfam_1(A_12)) | k1_xboole_0=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.27/1.31  tff(c_284, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(splitRight, [status(thm)], [c_201])).
% 2.27/1.31  tff(c_286, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_284, c_240])).
% 2.27/1.31  tff(c_298, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_286])).
% 2.27/1.31  tff(c_301, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_298])).
% 2.27/1.31  tff(c_303, plain, $false, inference(negUnitSimplification, [status(thm)], [c_285, c_301])).
% 2.27/1.31  tff(c_304, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_66])).
% 2.27/1.31  tff(c_307, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_304, c_24])).
% 2.27/1.31  tff(c_313, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_307])).
% 2.27/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.31  
% 2.27/1.31  Inference rules
% 2.27/1.31  ----------------------
% 2.27/1.31  #Ref     : 0
% 2.27/1.31  #Sup     : 55
% 2.27/1.31  #Fact    : 0
% 2.27/1.31  #Define  : 0
% 2.27/1.31  #Split   : 5
% 2.27/1.31  #Chain   : 0
% 2.27/1.31  #Close   : 0
% 2.27/1.31  
% 2.27/1.31  Ordering : KBO
% 2.27/1.31  
% 2.27/1.31  Simplification rules
% 2.27/1.31  ----------------------
% 2.27/1.31  #Subsume      : 0
% 2.27/1.31  #Demod        : 47
% 2.27/1.31  #Tautology    : 33
% 2.27/1.31  #SimpNegUnit  : 1
% 2.27/1.31  #BackRed      : 21
% 2.27/1.31  
% 2.27/1.31  #Partial instantiations: 0
% 2.27/1.31  #Strategies tried      : 1
% 2.27/1.31  
% 2.27/1.31  Timing (in seconds)
% 2.27/1.31  ----------------------
% 2.27/1.31  Preprocessing        : 0.29
% 2.27/1.31  Parsing              : 0.15
% 2.27/1.31  CNF conversion       : 0.02
% 2.27/1.31  Main loop            : 0.21
% 2.27/1.31  Inferencing          : 0.07
% 2.27/1.31  Reduction            : 0.07
% 2.27/1.31  Demodulation         : 0.05
% 2.27/1.31  BG Simplification    : 0.01
% 2.27/1.31  Subsumption          : 0.04
% 2.27/1.31  Abstraction          : 0.01
% 2.27/1.31  MUC search           : 0.00
% 2.27/1.31  Cooper               : 0.00
% 2.27/1.31  Total                : 0.53
% 2.27/1.31  Index Insertion      : 0.00
% 2.27/1.31  Index Deletion       : 0.00
% 2.27/1.31  Index Matching       : 0.00
% 2.27/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
