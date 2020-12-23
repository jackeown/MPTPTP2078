%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:59 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 194 expanded)
%              Number of leaves         :   21 (  71 expanded)
%              Depth                    :    9
%              Number of atoms          :   93 ( 393 expanded)
%              Number of equality atoms :   39 ( 157 expanded)
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

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k6_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_setfam_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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

tff(c_163,plain,(
    ! [A_34,B_35] :
      ( m1_subset_1(k6_setfam_1(A_34,B_35),k1_zfmisc_1(A_34))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(k1_zfmisc_1(A_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_179,plain,
    ( m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_163])).

tff(c_186,plain,(
    m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_179])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_192,plain,(
    r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_186,c_18])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_112,plain,(
    k6_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_100])).

tff(c_205,plain,(
    ! [A_36,B_37] :
      ( k8_setfam_1(A_36,B_37) = k6_setfam_1(A_36,B_37)
      | k1_xboole_0 = B_37
      | ~ m1_subset_1(B_37,k1_zfmisc_1(k1_zfmisc_1(A_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_216,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k6_setfam_1('#skF_1','#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_205])).

tff(c_223,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_216])).

tff(c_226,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_223])).

tff(c_219,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k6_setfam_1('#skF_1','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_28,c_205])).

tff(c_225,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_219])).

tff(c_237,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_225])).

tff(c_238,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_237])).

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

tff(c_245,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_80])).

tff(c_255,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_245])).

tff(c_256,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_237])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

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

tff(c_230,plain,(
    ! [A_24] : k8_setfam_1(A_24,'#skF_2') = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_88])).

tff(c_24,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_269,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_24])).

tff(c_292,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_269])).

tff(c_295,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_292])).

tff(c_297,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_223])).

tff(c_22,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k1_setfam_1(B_13),k1_setfam_1(A_12))
      | k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_303,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_225])).

tff(c_310,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_8])).

tff(c_318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_80])).

tff(c_319,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_225])).

tff(c_296,plain,(
    k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_223])).

tff(c_298,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_24])).

tff(c_321,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_298])).

tff(c_328,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_321])).

tff(c_331,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_328])).

tff(c_333,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_297,c_331])).

tff(c_334,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_337,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_24])).

tff(c_343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_337])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:28:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.39/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.44  
% 2.39/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.44  %$ r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.39/1.44  
% 2.39/1.44  %Foreground sorts:
% 2.39/1.44  
% 2.39/1.44  
% 2.39/1.44  %Background operators:
% 2.39/1.44  
% 2.39/1.44  
% 2.39/1.44  %Foreground operators:
% 2.39/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.39/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.39/1.44  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.39/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.39/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.39/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.39/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.39/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.39/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.39/1.44  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.39/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.39/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.39/1.44  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.39/1.44  
% 2.51/1.46  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.51/1.46  tff(f_72, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_setfam_1)).
% 2.51/1.46  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 2.51/1.46  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k6_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_setfam_1)).
% 2.51/1.46  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.51/1.46  tff(f_44, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 2.51/1.46  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.51/1.46  tff(f_62, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 2.51/1.46  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.51/1.46  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.51/1.46  tff(c_100, plain, (![A_26, B_27]: (k6_setfam_1(A_26, B_27)=k1_setfam_1(B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(k1_zfmisc_1(A_26))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.51/1.46  tff(c_113, plain, (k6_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_100])).
% 2.51/1.46  tff(c_163, plain, (![A_34, B_35]: (m1_subset_1(k6_setfam_1(A_34, B_35), k1_zfmisc_1(A_34)) | ~m1_subset_1(B_35, k1_zfmisc_1(k1_zfmisc_1(A_34))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.51/1.46  tff(c_179, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_113, c_163])).
% 2.51/1.46  tff(c_186, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_179])).
% 2.51/1.46  tff(c_18, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.51/1.46  tff(c_192, plain, (r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_186, c_18])).
% 2.51/1.46  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.51/1.46  tff(c_112, plain, (k6_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(resolution, [status(thm)], [c_30, c_100])).
% 2.51/1.46  tff(c_205, plain, (![A_36, B_37]: (k8_setfam_1(A_36, B_37)=k6_setfam_1(A_36, B_37) | k1_xboole_0=B_37 | ~m1_subset_1(B_37, k1_zfmisc_1(k1_zfmisc_1(A_36))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.51/1.46  tff(c_216, plain, (k8_setfam_1('#skF_1', '#skF_2')=k6_setfam_1('#skF_1', '#skF_2') | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_205])).
% 2.51/1.46  tff(c_223, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_216])).
% 2.51/1.46  tff(c_226, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_223])).
% 2.51/1.46  tff(c_219, plain, (k8_setfam_1('#skF_1', '#skF_3')=k6_setfam_1('#skF_1', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_28, c_205])).
% 2.51/1.46  tff(c_225, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_113, c_219])).
% 2.51/1.46  tff(c_237, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_226, c_225])).
% 2.51/1.46  tff(c_238, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_237])).
% 2.51/1.46  tff(c_26, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.51/1.46  tff(c_48, plain, (![B_21, A_22]: (B_21=A_22 | ~r1_tarski(B_21, A_22) | ~r1_tarski(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.51/1.46  tff(c_66, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_48])).
% 2.51/1.46  tff(c_80, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_66])).
% 2.51/1.46  tff(c_245, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_238, c_80])).
% 2.51/1.46  tff(c_255, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_245])).
% 2.51/1.46  tff(c_256, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_237])).
% 2.51/1.46  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.51/1.46  tff(c_20, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.51/1.46  tff(c_82, plain, (![A_24]: (k8_setfam_1(A_24, k1_xboole_0)=A_24 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_24))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.51/1.46  tff(c_85, plain, (![A_24]: (k8_setfam_1(A_24, k1_xboole_0)=A_24 | ~r1_tarski(k1_xboole_0, k1_zfmisc_1(A_24)))), inference(resolution, [status(thm)], [c_20, c_82])).
% 2.51/1.46  tff(c_88, plain, (![A_24]: (k8_setfam_1(A_24, k1_xboole_0)=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_85])).
% 2.51/1.46  tff(c_230, plain, (![A_24]: (k8_setfam_1(A_24, '#skF_2')=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_226, c_88])).
% 2.51/1.46  tff(c_24, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.51/1.46  tff(c_269, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_230, c_24])).
% 2.51/1.46  tff(c_292, plain, (~r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_256, c_269])).
% 2.51/1.46  tff(c_295, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_192, c_292])).
% 2.51/1.46  tff(c_297, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_223])).
% 2.51/1.46  tff(c_22, plain, (![B_13, A_12]: (r1_tarski(k1_setfam_1(B_13), k1_setfam_1(A_12)) | k1_xboole_0=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.51/1.46  tff(c_303, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_225])).
% 2.51/1.46  tff(c_310, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_303, c_8])).
% 2.51/1.46  tff(c_318, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_310, c_80])).
% 2.51/1.46  tff(c_319, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_225])).
% 2.51/1.46  tff(c_296, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(splitRight, [status(thm)], [c_223])).
% 2.51/1.46  tff(c_298, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_296, c_24])).
% 2.51/1.46  tff(c_321, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_319, c_298])).
% 2.51/1.46  tff(c_328, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_321])).
% 2.51/1.46  tff(c_331, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_328])).
% 2.51/1.46  tff(c_333, plain, $false, inference(negUnitSimplification, [status(thm)], [c_297, c_331])).
% 2.51/1.46  tff(c_334, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_66])).
% 2.51/1.46  tff(c_337, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_334, c_24])).
% 2.51/1.46  tff(c_343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_337])).
% 2.51/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.46  
% 2.51/1.46  Inference rules
% 2.51/1.46  ----------------------
% 2.51/1.46  #Ref     : 0
% 2.51/1.46  #Sup     : 58
% 2.51/1.46  #Fact    : 0
% 2.51/1.46  #Define  : 0
% 2.51/1.46  #Split   : 8
% 2.51/1.46  #Chain   : 0
% 2.51/1.46  #Close   : 0
% 2.51/1.46  
% 2.51/1.46  Ordering : KBO
% 2.51/1.46  
% 2.51/1.46  Simplification rules
% 2.51/1.46  ----------------------
% 2.51/1.46  #Subsume      : 2
% 2.51/1.46  #Demod        : 60
% 2.51/1.46  #Tautology    : 37
% 2.51/1.46  #SimpNegUnit  : 1
% 2.51/1.46  #BackRed      : 33
% 2.51/1.46  
% 2.51/1.46  #Partial instantiations: 0
% 2.51/1.46  #Strategies tried      : 1
% 2.51/1.46  
% 2.51/1.46  Timing (in seconds)
% 2.51/1.46  ----------------------
% 2.51/1.46  Preprocessing        : 0.32
% 2.51/1.46  Parsing              : 0.17
% 2.51/1.46  CNF conversion       : 0.02
% 2.51/1.46  Main loop            : 0.24
% 2.51/1.46  Inferencing          : 0.08
% 2.51/1.46  Reduction            : 0.08
% 2.51/1.46  Demodulation         : 0.06
% 2.51/1.46  BG Simplification    : 0.01
% 2.51/1.46  Subsumption          : 0.05
% 2.51/1.46  Abstraction          : 0.01
% 2.51/1.46  MUC search           : 0.00
% 2.51/1.46  Cooper               : 0.00
% 2.51/1.46  Total                : 0.59
% 2.51/1.46  Index Insertion      : 0.00
% 2.51/1.46  Index Deletion       : 0.00
% 2.51/1.46  Index Matching       : 0.00
% 2.51/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
