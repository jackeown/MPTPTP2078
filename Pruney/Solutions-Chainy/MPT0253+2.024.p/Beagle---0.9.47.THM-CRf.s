%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:17 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :   33 (  36 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 (  57 expanded)
%              Number of equality atoms :   13 (  16 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k2_xboole_0(k2_tarski(A,C),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B)
        & ! [D] :
            ( ( r1_tarski(A,D)
              & r1_tarski(C,D) )
           => r1_tarski(B,D) ) )
     => B = k2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_24,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_22,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_14,plain,(
    ! [A_11,B_12,C_13] :
      ( r1_tarski(k2_tarski(A_11,B_12),C_13)
      | ~ r2_hidden(B_12,C_13)
      | ~ r2_hidden(A_11,C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_35,plain,(
    ! [A_15,B_16] : r1_tarski(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_38,plain,(
    ! [A_3] : r1_tarski(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_35])).

tff(c_206,plain,(
    ! [A_50,B_51,C_52] :
      ( r1_tarski(A_50,'#skF_1'(A_50,B_51,C_52))
      | k2_xboole_0(A_50,C_52) = B_51
      | ~ r1_tarski(C_52,B_51)
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    ! [B_6,A_5,C_7] :
      ( ~ r1_tarski(B_6,'#skF_1'(A_5,B_6,C_7))
      | k2_xboole_0(A_5,C_7) = B_6
      | ~ r1_tarski(C_7,B_6)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_210,plain,(
    ! [B_51,C_52] :
      ( k2_xboole_0(B_51,C_52) = B_51
      | ~ r1_tarski(C_52,B_51)
      | ~ r1_tarski(B_51,B_51) ) ),
    inference(resolution,[status(thm)],[c_206,c_6])).

tff(c_224,plain,(
    ! [B_53,C_54] :
      ( k2_xboole_0(B_53,C_54) = B_53
      | ~ r1_tarski(C_54,B_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_210])).

tff(c_1992,plain,(
    ! [C_107,A_108,B_109] :
      ( k2_xboole_0(C_107,k2_tarski(A_108,B_109)) = C_107
      | ~ r2_hidden(B_109,C_107)
      | ~ r2_hidden(A_108,C_107) ) ),
    inference(resolution,[status(thm)],[c_14,c_224])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_4'),'#skF_3') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_25,plain,(
    k2_xboole_0('#skF_3',k2_tarski('#skF_2','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20])).

tff(c_2080,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | ~ r2_hidden('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1992,c_25])).

tff(c_2161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_2080])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:09:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.52/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.54  
% 3.52/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.54  %$ r2_hidden > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.52/1.54  
% 3.52/1.54  %Foreground sorts:
% 3.52/1.54  
% 3.52/1.54  
% 3.52/1.54  %Background operators:
% 3.52/1.54  
% 3.52/1.54  
% 3.52/1.54  %Foreground operators:
% 3.52/1.54  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.52/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.52/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.52/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.52/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.52/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.52/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.52/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.52/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.52/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.52/1.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.52/1.54  
% 3.52/1.55  tff(f_57, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k2_xboole_0(k2_tarski(A, C), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 3.52/1.55  tff(f_50, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.52/1.55  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.52/1.55  tff(f_44, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.52/1.55  tff(f_42, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(C, B)) & (![D]: ((r1_tarski(A, D) & r1_tarski(C, D)) => r1_tarski(B, D)))) => (B = k2_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_xboole_1)).
% 3.52/1.55  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.52/1.55  tff(c_24, plain, (r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.52/1.55  tff(c_22, plain, (r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.52/1.55  tff(c_14, plain, (![A_11, B_12, C_13]: (r1_tarski(k2_tarski(A_11, B_12), C_13) | ~r2_hidden(B_12, C_13) | ~r2_hidden(A_11, C_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.52/1.55  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.52/1.55  tff(c_35, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.52/1.55  tff(c_38, plain, (![A_3]: (r1_tarski(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_35])).
% 3.52/1.55  tff(c_206, plain, (![A_50, B_51, C_52]: (r1_tarski(A_50, '#skF_1'(A_50, B_51, C_52)) | k2_xboole_0(A_50, C_52)=B_51 | ~r1_tarski(C_52, B_51) | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.52/1.55  tff(c_6, plain, (![B_6, A_5, C_7]: (~r1_tarski(B_6, '#skF_1'(A_5, B_6, C_7)) | k2_xboole_0(A_5, C_7)=B_6 | ~r1_tarski(C_7, B_6) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.52/1.55  tff(c_210, plain, (![B_51, C_52]: (k2_xboole_0(B_51, C_52)=B_51 | ~r1_tarski(C_52, B_51) | ~r1_tarski(B_51, B_51))), inference(resolution, [status(thm)], [c_206, c_6])).
% 3.52/1.55  tff(c_224, plain, (![B_53, C_54]: (k2_xboole_0(B_53, C_54)=B_53 | ~r1_tarski(C_54, B_53))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_210])).
% 3.52/1.55  tff(c_1992, plain, (![C_107, A_108, B_109]: (k2_xboole_0(C_107, k2_tarski(A_108, B_109))=C_107 | ~r2_hidden(B_109, C_107) | ~r2_hidden(A_108, C_107))), inference(resolution, [status(thm)], [c_14, c_224])).
% 3.52/1.55  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.52/1.55  tff(c_20, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_4'), '#skF_3')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.52/1.55  tff(c_25, plain, (k2_xboole_0('#skF_3', k2_tarski('#skF_2', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20])).
% 3.52/1.55  tff(c_2080, plain, (~r2_hidden('#skF_4', '#skF_3') | ~r2_hidden('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1992, c_25])).
% 3.52/1.55  tff(c_2161, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_2080])).
% 3.52/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.55  
% 3.52/1.55  Inference rules
% 3.52/1.55  ----------------------
% 3.52/1.55  #Ref     : 0
% 3.52/1.55  #Sup     : 498
% 3.52/1.55  #Fact    : 0
% 3.52/1.55  #Define  : 0
% 3.52/1.55  #Split   : 0
% 3.52/1.55  #Chain   : 0
% 3.52/1.55  #Close   : 0
% 3.52/1.55  
% 3.52/1.55  Ordering : KBO
% 3.52/1.55  
% 3.52/1.55  Simplification rules
% 3.52/1.55  ----------------------
% 3.52/1.55  #Subsume      : 77
% 3.52/1.55  #Demod        : 734
% 3.52/1.55  #Tautology    : 360
% 3.52/1.55  #SimpNegUnit  : 0
% 3.52/1.55  #BackRed      : 0
% 3.52/1.55  
% 3.52/1.55  #Partial instantiations: 0
% 3.52/1.55  #Strategies tried      : 1
% 3.52/1.55  
% 3.52/1.55  Timing (in seconds)
% 3.52/1.55  ----------------------
% 3.52/1.55  Preprocessing        : 0.26
% 3.52/1.55  Parsing              : 0.15
% 3.52/1.55  CNF conversion       : 0.02
% 3.52/1.55  Main loop            : 0.53
% 3.52/1.55  Inferencing          : 0.18
% 3.52/1.55  Reduction            : 0.24
% 3.52/1.55  Demodulation         : 0.20
% 3.52/1.55  BG Simplification    : 0.02
% 3.52/1.55  Subsumption          : 0.08
% 3.52/1.55  Abstraction          : 0.03
% 3.52/1.55  MUC search           : 0.00
% 3.52/1.55  Cooper               : 0.00
% 3.52/1.55  Total                : 0.82
% 3.52/1.55  Index Insertion      : 0.00
% 3.52/1.55  Index Deletion       : 0.00
% 3.52/1.55  Index Matching       : 0.00
% 3.52/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
