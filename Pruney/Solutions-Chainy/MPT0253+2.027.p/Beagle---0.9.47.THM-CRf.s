%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:17 EST 2020

% Result     : Theorem 10.94s
% Output     : CNFRefutation 11.00s
% Verified   : 
% Statistics : Number of formulae       :   35 (  45 expanded)
%              Number of leaves         :   15 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :   36 (  51 expanded)
%              Number of equality atoms :   21 (  31 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k2_xboole_0(k2_tarski(A,C),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(c_12,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_70,plain,(
    ! [A_14,B_15] :
      ( k2_xboole_0(k1_tarski(A_14),B_15) = B_15
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_80,plain,(
    ! [B_15,A_14] :
      ( k2_xboole_0(B_15,k1_tarski(A_14)) = B_15
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_2])).

tff(c_14,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_49,plain,(
    ! [A_12,B_13] : k2_xboole_0(k1_tarski(A_12),k1_tarski(B_13)) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_55,plain,(
    ! [B_13,A_12] : k2_xboole_0(k1_tarski(B_13),k1_tarski(A_12)) = k2_tarski(A_12,B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_2])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k2_xboole_0(k2_xboole_0(A_3,B_4),C_5) = k2_xboole_0(A_3,k2_xboole_0(B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( k2_xboole_0(k1_tarski(A_8),B_9) = B_9
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_171,plain,(
    ! [A_20,B_21,C_22] : k2_xboole_0(k2_xboole_0(A_20,B_21),C_22) = k2_xboole_0(A_20,k2_xboole_0(B_21,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1119,plain,(
    ! [A_41,B_42,C_43] :
      ( k2_xboole_0(k1_tarski(A_41),k2_xboole_0(B_42,C_43)) = k2_xboole_0(B_42,C_43)
      | ~ r2_hidden(A_41,B_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_171])).

tff(c_1252,plain,(
    ! [B_42,C_43,A_41] :
      ( k2_xboole_0(k2_xboole_0(B_42,C_43),k1_tarski(A_41)) = k2_xboole_0(B_42,C_43)
      | ~ r2_hidden(A_41,B_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1119])).

tff(c_2620,plain,(
    ! [B_59,C_60,A_61] :
      ( k2_xboole_0(B_59,k2_xboole_0(C_60,k1_tarski(A_61))) = k2_xboole_0(B_59,C_60)
      | ~ r2_hidden(A_61,B_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1252])).

tff(c_12948,plain,(
    ! [B_151,A_152,B_153] :
      ( k2_xboole_0(B_151,k2_tarski(A_152,B_153)) = k2_xboole_0(B_151,k1_tarski(B_153))
      | ~ r2_hidden(A_152,B_151) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_2620])).

tff(c_10,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_15,plain,(
    k2_xboole_0('#skF_2',k2_tarski('#skF_1','#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10])).

tff(c_13126,plain,
    ( k2_xboole_0('#skF_2',k1_tarski('#skF_3')) != '#skF_2'
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12948,c_15])).

tff(c_13256,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_13126])).

tff(c_13277,plain,(
    ~ r2_hidden('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_13256])).

tff(c_13281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_13277])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:01:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.94/4.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.94/4.46  
% 10.94/4.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.94/4.46  %$ r2_hidden > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 10.94/4.46  
% 10.94/4.46  %Foreground sorts:
% 10.94/4.46  
% 10.94/4.46  
% 10.94/4.46  %Background operators:
% 10.94/4.46  
% 10.94/4.46  
% 10.94/4.46  %Foreground operators:
% 10.94/4.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.94/4.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.94/4.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.94/4.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.94/4.46  tff('#skF_2', type, '#skF_2': $i).
% 10.94/4.46  tff('#skF_3', type, '#skF_3': $i).
% 10.94/4.46  tff('#skF_1', type, '#skF_1': $i).
% 10.94/4.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.94/4.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.94/4.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.94/4.46  
% 11.00/4.47  tff(f_42, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k2_xboole_0(k2_tarski(A, C), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 11.00/4.47  tff(f_35, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 11.00/4.47  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 11.00/4.47  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 11.00/4.47  tff(f_29, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 11.00/4.47  tff(c_12, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.00/4.47  tff(c_70, plain, (![A_14, B_15]: (k2_xboole_0(k1_tarski(A_14), B_15)=B_15 | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.00/4.47  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.00/4.47  tff(c_80, plain, (![B_15, A_14]: (k2_xboole_0(B_15, k1_tarski(A_14))=B_15 | ~r2_hidden(A_14, B_15))), inference(superposition, [status(thm), theory('equality')], [c_70, c_2])).
% 11.00/4.47  tff(c_14, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.00/4.47  tff(c_49, plain, (![A_12, B_13]: (k2_xboole_0(k1_tarski(A_12), k1_tarski(B_13))=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.00/4.47  tff(c_55, plain, (![B_13, A_12]: (k2_xboole_0(k1_tarski(B_13), k1_tarski(A_12))=k2_tarski(A_12, B_13))), inference(superposition, [status(thm), theory('equality')], [c_49, c_2])).
% 11.00/4.47  tff(c_4, plain, (![A_3, B_4, C_5]: (k2_xboole_0(k2_xboole_0(A_3, B_4), C_5)=k2_xboole_0(A_3, k2_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.00/4.47  tff(c_8, plain, (![A_8, B_9]: (k2_xboole_0(k1_tarski(A_8), B_9)=B_9 | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.00/4.47  tff(c_171, plain, (![A_20, B_21, C_22]: (k2_xboole_0(k2_xboole_0(A_20, B_21), C_22)=k2_xboole_0(A_20, k2_xboole_0(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.00/4.47  tff(c_1119, plain, (![A_41, B_42, C_43]: (k2_xboole_0(k1_tarski(A_41), k2_xboole_0(B_42, C_43))=k2_xboole_0(B_42, C_43) | ~r2_hidden(A_41, B_42))), inference(superposition, [status(thm), theory('equality')], [c_8, c_171])).
% 11.00/4.47  tff(c_1252, plain, (![B_42, C_43, A_41]: (k2_xboole_0(k2_xboole_0(B_42, C_43), k1_tarski(A_41))=k2_xboole_0(B_42, C_43) | ~r2_hidden(A_41, B_42))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1119])).
% 11.00/4.47  tff(c_2620, plain, (![B_59, C_60, A_61]: (k2_xboole_0(B_59, k2_xboole_0(C_60, k1_tarski(A_61)))=k2_xboole_0(B_59, C_60) | ~r2_hidden(A_61, B_59))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1252])).
% 11.00/4.47  tff(c_12948, plain, (![B_151, A_152, B_153]: (k2_xboole_0(B_151, k2_tarski(A_152, B_153))=k2_xboole_0(B_151, k1_tarski(B_153)) | ~r2_hidden(A_152, B_151))), inference(superposition, [status(thm), theory('equality')], [c_55, c_2620])).
% 11.00/4.47  tff(c_10, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.00/4.47  tff(c_15, plain, (k2_xboole_0('#skF_2', k2_tarski('#skF_1', '#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_10])).
% 11.00/4.47  tff(c_13126, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_3'))!='#skF_2' | ~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12948, c_15])).
% 11.00/4.47  tff(c_13256, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_13126])).
% 11.00/4.47  tff(c_13277, plain, (~r2_hidden('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_80, c_13256])).
% 11.00/4.47  tff(c_13281, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_13277])).
% 11.00/4.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.00/4.47  
% 11.00/4.47  Inference rules
% 11.00/4.47  ----------------------
% 11.00/4.47  #Ref     : 0
% 11.00/4.47  #Sup     : 3464
% 11.00/4.47  #Fact    : 0
% 11.00/4.47  #Define  : 0
% 11.00/4.47  #Split   : 0
% 11.00/4.47  #Chain   : 0
% 11.00/4.47  #Close   : 0
% 11.00/4.47  
% 11.00/4.47  Ordering : KBO
% 11.00/4.47  
% 11.00/4.47  Simplification rules
% 11.00/4.47  ----------------------
% 11.00/4.47  #Subsume      : 467
% 11.00/4.47  #Demod        : 1689
% 11.00/4.47  #Tautology    : 355
% 11.00/4.47  #SimpNegUnit  : 0
% 11.00/4.47  #BackRed      : 0
% 11.00/4.47  
% 11.00/4.47  #Partial instantiations: 0
% 11.00/4.47  #Strategies tried      : 1
% 11.00/4.47  
% 11.00/4.47  Timing (in seconds)
% 11.00/4.47  ----------------------
% 11.00/4.47  Preprocessing        : 0.27
% 11.00/4.47  Parsing              : 0.15
% 11.00/4.47  CNF conversion       : 0.02
% 11.00/4.47  Main loop            : 3.37
% 11.00/4.47  Inferencing          : 0.66
% 11.00/4.48  Reduction            : 2.10
% 11.00/4.48  Demodulation         : 1.96
% 11.00/4.48  BG Simplification    : 0.11
% 11.00/4.48  Subsumption          : 0.39
% 11.00/4.48  Abstraction          : 0.18
% 11.00/4.48  MUC search           : 0.00
% 11.00/4.48  Cooper               : 0.00
% 11.00/4.48  Total                : 3.67
% 11.00/4.48  Index Insertion      : 0.00
% 11.00/4.48  Index Deletion       : 0.00
% 11.00/4.48  Index Matching       : 0.00
% 11.00/4.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
