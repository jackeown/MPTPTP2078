%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:36 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   48 (  50 expanded)
%              Number of leaves         :   27 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :   49 (  52 expanded)
%              Number of equality atoms :   17 (  18 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_72,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(c_40,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_32,plain,(
    ! [A_24,B_25] :
      ( r1_xboole_0(k1_tarski(A_24),B_25)
      | r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_16,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [B_13,A_12] : k2_tarski(B_13,A_12) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_99,plain,(
    ! [A_42,B_43] : k3_tarski(k2_tarski(A_42,B_43)) = k2_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_152,plain,(
    ! [A_49,B_50] : k3_tarski(k2_tarski(A_49,B_50)) = k2_xboole_0(B_50,A_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_99])).

tff(c_34,plain,(
    ! [A_26,B_27] : k3_tarski(k2_tarski(A_26,B_27)) = k2_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_158,plain,(
    ! [B_50,A_49] : k2_xboole_0(B_50,A_49) = k2_xboole_0(A_49,B_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_34])).

tff(c_42,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_1'),'#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_194,plain,(
    r1_tarski(k2_xboole_0('#skF_2',k1_tarski('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_42])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_252,plain,
    ( k2_xboole_0('#skF_2',k1_tarski('#skF_1')) = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_xboole_0('#skF_2',k1_tarski('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_194,c_2])).

tff(c_255,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_252])).

tff(c_283,plain,(
    ! [A_59,C_60,B_61] :
      ( r1_xboole_0(A_59,C_60)
      | ~ r1_xboole_0(A_59,k2_xboole_0(B_61,C_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_306,plain,(
    ! [A_62] :
      ( r1_xboole_0(A_62,k1_tarski('#skF_1'))
      | ~ r1_xboole_0(A_62,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_283])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = A_10
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_366,plain,(
    ! [A_70] :
      ( k4_xboole_0(A_70,k1_tarski('#skF_1')) = A_70
      | ~ r1_xboole_0(A_70,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_306,c_18])).

tff(c_36,plain,(
    ! [B_29] : k4_xboole_0(k1_tarski(B_29),k1_tarski(B_29)) != k1_tarski(B_29) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_387,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_366,c_36])).

tff(c_395,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_387])).

tff(c_400,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_395])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:09:25 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.38  
% 2.24/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.39  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 2.24/1.39  
% 2.24/1.39  %Foreground sorts:
% 2.24/1.39  
% 2.24/1.39  
% 2.24/1.39  %Background operators:
% 2.24/1.39  
% 2.24/1.39  
% 2.24/1.39  %Foreground operators:
% 2.24/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.24/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.24/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.24/1.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.24/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.24/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.24/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.24/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.24/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.24/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.24/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.24/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.39  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.24/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.24/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.24/1.39  
% 2.42/1.41  tff(f_82, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 2.42/1.41  tff(f_70, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.42/1.41  tff(f_51, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.42/1.41  tff(f_57, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.42/1.41  tff(f_72, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.42/1.41  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.42/1.41  tff(f_49, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 2.42/1.41  tff(f_55, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.42/1.41  tff(f_77, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.42/1.41  tff(c_40, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.42/1.41  tff(c_32, plain, (![A_24, B_25]: (r1_xboole_0(k1_tarski(A_24), B_25) | r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.42/1.41  tff(c_16, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.42/1.41  tff(c_22, plain, (![B_13, A_12]: (k2_tarski(B_13, A_12)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.42/1.41  tff(c_99, plain, (![A_42, B_43]: (k3_tarski(k2_tarski(A_42, B_43))=k2_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.42/1.41  tff(c_152, plain, (![A_49, B_50]: (k3_tarski(k2_tarski(A_49, B_50))=k2_xboole_0(B_50, A_49))), inference(superposition, [status(thm), theory('equality')], [c_22, c_99])).
% 2.42/1.41  tff(c_34, plain, (![A_26, B_27]: (k3_tarski(k2_tarski(A_26, B_27))=k2_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.42/1.41  tff(c_158, plain, (![B_50, A_49]: (k2_xboole_0(B_50, A_49)=k2_xboole_0(A_49, B_50))), inference(superposition, [status(thm), theory('equality')], [c_152, c_34])).
% 2.42/1.41  tff(c_42, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.42/1.41  tff(c_194, plain, (r1_tarski(k2_xboole_0('#skF_2', k1_tarski('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_42])).
% 2.42/1.41  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.42/1.41  tff(c_252, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))='#skF_2' | ~r1_tarski('#skF_2', k2_xboole_0('#skF_2', k1_tarski('#skF_1')))), inference(resolution, [status(thm)], [c_194, c_2])).
% 2.42/1.41  tff(c_255, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_252])).
% 2.42/1.41  tff(c_283, plain, (![A_59, C_60, B_61]: (r1_xboole_0(A_59, C_60) | ~r1_xboole_0(A_59, k2_xboole_0(B_61, C_60)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.42/1.41  tff(c_306, plain, (![A_62]: (r1_xboole_0(A_62, k1_tarski('#skF_1')) | ~r1_xboole_0(A_62, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_255, c_283])).
% 2.42/1.41  tff(c_18, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=A_10 | ~r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.42/1.41  tff(c_366, plain, (![A_70]: (k4_xboole_0(A_70, k1_tarski('#skF_1'))=A_70 | ~r1_xboole_0(A_70, '#skF_2'))), inference(resolution, [status(thm)], [c_306, c_18])).
% 2.42/1.41  tff(c_36, plain, (![B_29]: (k4_xboole_0(k1_tarski(B_29), k1_tarski(B_29))!=k1_tarski(B_29))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.42/1.41  tff(c_387, plain, (~r1_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_366, c_36])).
% 2.42/1.41  tff(c_395, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_387])).
% 2.42/1.41  tff(c_400, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_395])).
% 2.42/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.41  
% 2.42/1.41  Inference rules
% 2.42/1.41  ----------------------
% 2.42/1.41  #Ref     : 0
% 2.42/1.41  #Sup     : 84
% 2.42/1.41  #Fact    : 0
% 2.42/1.41  #Define  : 0
% 2.42/1.41  #Split   : 1
% 2.42/1.41  #Chain   : 0
% 2.42/1.41  #Close   : 0
% 2.42/1.41  
% 2.42/1.41  Ordering : KBO
% 2.42/1.41  
% 2.42/1.41  Simplification rules
% 2.42/1.41  ----------------------
% 2.42/1.41  #Subsume      : 8
% 2.42/1.41  #Demod        : 19
% 2.42/1.41  #Tautology    : 54
% 2.42/1.41  #SimpNegUnit  : 1
% 2.42/1.41  #BackRed      : 2
% 2.42/1.41  
% 2.42/1.41  #Partial instantiations: 0
% 2.42/1.41  #Strategies tried      : 1
% 2.42/1.41  
% 2.42/1.41  Timing (in seconds)
% 2.42/1.41  ----------------------
% 2.42/1.42  Preprocessing        : 0.38
% 2.42/1.42  Parsing              : 0.21
% 2.42/1.42  CNF conversion       : 0.02
% 2.42/1.42  Main loop            : 0.24
% 2.42/1.42  Inferencing          : 0.09
% 2.42/1.42  Reduction            : 0.09
% 2.42/1.42  Demodulation         : 0.06
% 2.42/1.42  BG Simplification    : 0.02
% 2.42/1.42  Subsumption          : 0.04
% 2.42/1.42  Abstraction          : 0.02
% 2.42/1.42  MUC search           : 0.00
% 2.42/1.42  Cooper               : 0.00
% 2.42/1.42  Total                : 0.67
% 2.42/1.42  Index Insertion      : 0.00
% 2.42/1.42  Index Deletion       : 0.00
% 2.42/1.42  Index Matching       : 0.00
% 2.42/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
