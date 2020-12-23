%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:09 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   52 (  82 expanded)
%              Number of leaves         :   25 (  40 expanded)
%              Depth                    :    7
%              Number of atoms          :   47 ( 100 expanded)
%              Number of equality atoms :   32 (  80 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_zfmisc_1(k1_tarski(A),k1_tarski(B)) = k1_tarski(k4_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,k2_zfmisc_1(A,B))
        | r1_tarski(A,k2_zfmisc_1(B,A)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_32,plain,(
    k4_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_48,plain,(
    ! [A_25,B_26] : k1_mcart_1(k4_tarski(A_25,B_26)) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_57,plain,(
    k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_48])).

tff(c_73,plain,(
    ! [A_28,B_29] : k2_mcart_1(k4_tarski(A_28,B_29)) = B_29 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_82,plain,(
    k2_mcart_1('#skF_1') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_73])).

tff(c_30,plain,
    ( k2_mcart_1('#skF_1') = '#skF_1'
    | k1_mcart_1('#skF_1') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_94,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_82,c_30])).

tff(c_95,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_97,plain,(
    k4_tarski('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_32])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_89,plain,(
    ! [A_30,B_31] : k2_xboole_0(k1_tarski(A_30),B_31) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_93,plain,(
    ! [A_30] : k1_tarski(A_30) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_89])).

tff(c_168,plain,(
    ! [A_47,B_48] : k2_zfmisc_1(k1_tarski(A_47),k1_tarski(B_48)) = k1_tarski(k4_tarski(A_47,B_48)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( ~ r1_tarski(A_13,k2_zfmisc_1(A_13,B_14))
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_174,plain,(
    ! [A_47,B_48] :
      ( ~ r1_tarski(k1_tarski(A_47),k1_tarski(k4_tarski(A_47,B_48)))
      | k1_tarski(A_47) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_20])).

tff(c_185,plain,(
    ! [A_49,B_50] : ~ r1_tarski(k1_tarski(A_49),k1_tarski(k4_tarski(A_49,B_50))) ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_174])).

tff(c_188,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_185])).

tff(c_191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_188])).

tff(c_192,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_195,plain,(
    k4_tarski('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_32])).

tff(c_266,plain,(
    ! [A_66,B_67] : k2_zfmisc_1(k1_tarski(A_66),k1_tarski(B_67)) = k1_tarski(k4_tarski(A_66,B_67)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( ~ r1_tarski(A_13,k2_zfmisc_1(B_14,A_13))
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_272,plain,(
    ! [B_67,A_66] :
      ( ~ r1_tarski(k1_tarski(B_67),k1_tarski(k4_tarski(A_66,B_67)))
      | k1_tarski(B_67) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_18])).

tff(c_283,plain,(
    ! [B_68,A_69] : ~ r1_tarski(k1_tarski(B_68),k1_tarski(k4_tarski(A_69,B_68))) ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_272])).

tff(c_286,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_283])).

tff(c_289,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_286])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:01:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.27  
% 1.98/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.28  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.98/1.28  
% 1.98/1.28  %Foreground sorts:
% 1.98/1.28  
% 1.98/1.28  
% 1.98/1.28  %Background operators:
% 1.98/1.28  
% 1.98/1.28  
% 1.98/1.28  %Foreground operators:
% 1.98/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.98/1.28  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.98/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.98/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.98/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.98/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.98/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.98/1.28  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.28  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.28  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.28  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.98/1.28  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.98/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.98/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.28  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.98/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.98/1.28  
% 1.98/1.29  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.98/1.29  tff(f_66, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 1.98/1.29  tff(f_56, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 1.98/1.29  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 1.98/1.29  tff(f_52, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.98/1.29  tff(f_49, axiom, (![A, B]: (k2_zfmisc_1(k1_tarski(A), k1_tarski(B)) = k1_tarski(k4_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_zfmisc_1)).
% 1.98/1.29  tff(f_47, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 1.98/1.29  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.98/1.29  tff(c_32, plain, (k4_tarski('#skF_2', '#skF_3')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.98/1.29  tff(c_48, plain, (![A_25, B_26]: (k1_mcart_1(k4_tarski(A_25, B_26))=A_25)), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.98/1.29  tff(c_57, plain, (k1_mcart_1('#skF_1')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_32, c_48])).
% 1.98/1.29  tff(c_73, plain, (![A_28, B_29]: (k2_mcart_1(k4_tarski(A_28, B_29))=B_29)), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.98/1.29  tff(c_82, plain, (k2_mcart_1('#skF_1')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_32, c_73])).
% 1.98/1.29  tff(c_30, plain, (k2_mcart_1('#skF_1')='#skF_1' | k1_mcart_1('#skF_1')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.98/1.29  tff(c_94, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_57, c_82, c_30])).
% 1.98/1.29  tff(c_95, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_94])).
% 1.98/1.29  tff(c_97, plain, (k4_tarski('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_95, c_32])).
% 1.98/1.29  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.98/1.29  tff(c_89, plain, (![A_30, B_31]: (k2_xboole_0(k1_tarski(A_30), B_31)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.98/1.29  tff(c_93, plain, (![A_30]: (k1_tarski(A_30)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_89])).
% 1.98/1.29  tff(c_168, plain, (![A_47, B_48]: (k2_zfmisc_1(k1_tarski(A_47), k1_tarski(B_48))=k1_tarski(k4_tarski(A_47, B_48)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.98/1.29  tff(c_20, plain, (![A_13, B_14]: (~r1_tarski(A_13, k2_zfmisc_1(A_13, B_14)) | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.98/1.29  tff(c_174, plain, (![A_47, B_48]: (~r1_tarski(k1_tarski(A_47), k1_tarski(k4_tarski(A_47, B_48))) | k1_tarski(A_47)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_168, c_20])).
% 1.98/1.29  tff(c_185, plain, (![A_49, B_50]: (~r1_tarski(k1_tarski(A_49), k1_tarski(k4_tarski(A_49, B_50))))), inference(negUnitSimplification, [status(thm)], [c_93, c_174])).
% 1.98/1.29  tff(c_188, plain, (~r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_97, c_185])).
% 1.98/1.29  tff(c_191, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_188])).
% 1.98/1.29  tff(c_192, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_94])).
% 1.98/1.29  tff(c_195, plain, (k4_tarski('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_192, c_32])).
% 1.98/1.29  tff(c_266, plain, (![A_66, B_67]: (k2_zfmisc_1(k1_tarski(A_66), k1_tarski(B_67))=k1_tarski(k4_tarski(A_66, B_67)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.98/1.29  tff(c_18, plain, (![A_13, B_14]: (~r1_tarski(A_13, k2_zfmisc_1(B_14, A_13)) | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.98/1.29  tff(c_272, plain, (![B_67, A_66]: (~r1_tarski(k1_tarski(B_67), k1_tarski(k4_tarski(A_66, B_67))) | k1_tarski(B_67)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_266, c_18])).
% 1.98/1.29  tff(c_283, plain, (![B_68, A_69]: (~r1_tarski(k1_tarski(B_68), k1_tarski(k4_tarski(A_69, B_68))))), inference(negUnitSimplification, [status(thm)], [c_93, c_272])).
% 1.98/1.29  tff(c_286, plain, (~r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_195, c_283])).
% 1.98/1.29  tff(c_289, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_286])).
% 1.98/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.29  
% 1.98/1.29  Inference rules
% 1.98/1.29  ----------------------
% 1.98/1.29  #Ref     : 0
% 1.98/1.29  #Sup     : 63
% 1.98/1.29  #Fact    : 0
% 1.98/1.29  #Define  : 0
% 1.98/1.29  #Split   : 1
% 1.98/1.29  #Chain   : 0
% 1.98/1.29  #Close   : 0
% 1.98/1.29  
% 1.98/1.29  Ordering : KBO
% 1.98/1.29  
% 1.98/1.29  Simplification rules
% 1.98/1.29  ----------------------
% 1.98/1.29  #Subsume      : 0
% 1.98/1.29  #Demod        : 17
% 1.98/1.29  #Tautology    : 53
% 1.98/1.29  #SimpNegUnit  : 4
% 1.98/1.29  #BackRed      : 4
% 1.98/1.29  
% 1.98/1.29  #Partial instantiations: 0
% 1.98/1.29  #Strategies tried      : 1
% 1.98/1.29  
% 1.98/1.29  Timing (in seconds)
% 1.98/1.29  ----------------------
% 1.98/1.29  Preprocessing        : 0.31
% 1.98/1.29  Parsing              : 0.17
% 1.98/1.29  CNF conversion       : 0.02
% 1.98/1.29  Main loop            : 0.17
% 1.98/1.29  Inferencing          : 0.06
% 1.98/1.29  Reduction            : 0.06
% 1.98/1.29  Demodulation         : 0.04
% 1.98/1.29  BG Simplification    : 0.01
% 1.98/1.29  Subsumption          : 0.02
% 1.98/1.29  Abstraction          : 0.01
% 1.98/1.29  MUC search           : 0.00
% 1.98/1.29  Cooper               : 0.00
% 1.98/1.29  Total                : 0.51
% 1.98/1.29  Index Insertion      : 0.00
% 1.98/1.29  Index Deletion       : 0.00
% 1.98/1.29  Index Matching       : 0.00
% 1.98/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
