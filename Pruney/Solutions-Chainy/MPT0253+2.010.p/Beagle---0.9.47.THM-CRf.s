%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:15 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   40 (  43 expanded)
%              Number of leaves         :   22 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   38 (  45 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k2_xboole_0(k2_tarski(A,C),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_43,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_28,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_26,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_244,plain,(
    ! [A_50,B_51,C_52] :
      ( r1_tarski(k2_tarski(A_50,B_51),C_52)
      | ~ r2_hidden(B_51,C_52)
      | ~ r2_hidden(A_50,C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_272,plain,(
    ! [A_57,B_58,C_59] :
      ( k3_xboole_0(k2_tarski(A_57,B_58),C_59) = k2_tarski(A_57,B_58)
      | ~ r2_hidden(B_58,C_59)
      | ~ r2_hidden(A_57,C_59) ) ),
    inference(resolution,[status(thm)],[c_244,c_6])).

tff(c_71,plain,(
    ! [B_27,A_28] : k3_xboole_0(B_27,A_28) = k3_xboole_0(A_28,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_86,plain,(
    ! [A_28,B_27] : k2_xboole_0(A_28,k3_xboole_0(B_27,A_28)) = A_28 ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_4])).

tff(c_307,plain,(
    ! [C_60,A_61,B_62] :
      ( k2_xboole_0(C_60,k2_tarski(A_61,B_62)) = C_60
      | ~ r2_hidden(B_62,C_60)
      | ~ r2_hidden(A_61,C_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_86])).

tff(c_8,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_148,plain,(
    ! [A_35,B_36] : k3_tarski(k2_tarski(A_35,B_36)) = k2_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_163,plain,(
    ! [B_37,A_38] : k3_tarski(k2_tarski(B_37,A_38)) = k2_xboole_0(A_38,B_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_148])).

tff(c_16,plain,(
    ! [A_18,B_19] : k3_tarski(k2_tarski(A_18,B_19)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_169,plain,(
    ! [B_37,A_38] : k2_xboole_0(B_37,A_38) = k2_xboole_0(A_38,B_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_16])).

tff(c_24,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_186,plain,(
    k2_xboole_0('#skF_2',k2_tarski('#skF_1','#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_24])).

tff(c_313,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_186])).

tff(c_341,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_313])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:33:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.33  
% 2.20/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.33  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1
% 2.20/1.33  
% 2.20/1.33  %Foreground sorts:
% 2.20/1.33  
% 2.20/1.33  
% 2.20/1.33  %Background operators:
% 2.20/1.33  
% 2.20/1.33  
% 2.20/1.33  %Foreground operators:
% 2.20/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.20/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.20/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.20/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.20/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.20/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.20/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.20/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.20/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.20/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.33  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.20/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.20/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.20/1.33  
% 2.20/1.34  tff(f_56, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k2_xboole_0(k2_tarski(A, C), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 2.20/1.34  tff(f_49, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.20/1.34  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.20/1.34  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.20/1.34  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.20/1.34  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.20/1.34  tff(f_43, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.20/1.34  tff(c_28, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.20/1.34  tff(c_26, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.20/1.34  tff(c_244, plain, (![A_50, B_51, C_52]: (r1_tarski(k2_tarski(A_50, B_51), C_52) | ~r2_hidden(B_51, C_52) | ~r2_hidden(A_50, C_52))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.20/1.34  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.20/1.34  tff(c_272, plain, (![A_57, B_58, C_59]: (k3_xboole_0(k2_tarski(A_57, B_58), C_59)=k2_tarski(A_57, B_58) | ~r2_hidden(B_58, C_59) | ~r2_hidden(A_57, C_59))), inference(resolution, [status(thm)], [c_244, c_6])).
% 2.20/1.34  tff(c_71, plain, (![B_27, A_28]: (k3_xboole_0(B_27, A_28)=k3_xboole_0(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.20/1.34  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k3_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.20/1.34  tff(c_86, plain, (![A_28, B_27]: (k2_xboole_0(A_28, k3_xboole_0(B_27, A_28))=A_28)), inference(superposition, [status(thm), theory('equality')], [c_71, c_4])).
% 2.20/1.34  tff(c_307, plain, (![C_60, A_61, B_62]: (k2_xboole_0(C_60, k2_tarski(A_61, B_62))=C_60 | ~r2_hidden(B_62, C_60) | ~r2_hidden(A_61, C_60))), inference(superposition, [status(thm), theory('equality')], [c_272, c_86])).
% 2.20/1.34  tff(c_8, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.20/1.34  tff(c_148, plain, (![A_35, B_36]: (k3_tarski(k2_tarski(A_35, B_36))=k2_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.20/1.34  tff(c_163, plain, (![B_37, A_38]: (k3_tarski(k2_tarski(B_37, A_38))=k2_xboole_0(A_38, B_37))), inference(superposition, [status(thm), theory('equality')], [c_8, c_148])).
% 2.20/1.34  tff(c_16, plain, (![A_18, B_19]: (k3_tarski(k2_tarski(A_18, B_19))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.20/1.34  tff(c_169, plain, (![B_37, A_38]: (k2_xboole_0(B_37, A_38)=k2_xboole_0(A_38, B_37))), inference(superposition, [status(thm), theory('equality')], [c_163, c_16])).
% 2.20/1.34  tff(c_24, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.20/1.34  tff(c_186, plain, (k2_xboole_0('#skF_2', k2_tarski('#skF_1', '#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_169, c_24])).
% 2.20/1.34  tff(c_313, plain, (~r2_hidden('#skF_3', '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_307, c_186])).
% 2.20/1.34  tff(c_341, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_313])).
% 2.20/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.34  
% 2.20/1.34  Inference rules
% 2.20/1.34  ----------------------
% 2.20/1.34  #Ref     : 0
% 2.20/1.34  #Sup     : 78
% 2.20/1.34  #Fact    : 0
% 2.20/1.34  #Define  : 0
% 2.20/1.34  #Split   : 0
% 2.20/1.34  #Chain   : 0
% 2.20/1.34  #Close   : 0
% 2.20/1.34  
% 2.20/1.34  Ordering : KBO
% 2.20/1.34  
% 2.20/1.34  Simplification rules
% 2.20/1.34  ----------------------
% 2.20/1.34  #Subsume      : 7
% 2.20/1.34  #Demod        : 9
% 2.20/1.34  #Tautology    : 51
% 2.20/1.34  #SimpNegUnit  : 0
% 2.20/1.34  #BackRed      : 1
% 2.20/1.34  
% 2.20/1.34  #Partial instantiations: 0
% 2.20/1.34  #Strategies tried      : 1
% 2.20/1.34  
% 2.20/1.34  Timing (in seconds)
% 2.20/1.34  ----------------------
% 2.20/1.34  Preprocessing        : 0.35
% 2.20/1.34  Parsing              : 0.16
% 2.20/1.34  CNF conversion       : 0.03
% 2.20/1.34  Main loop            : 0.22
% 2.20/1.34  Inferencing          : 0.09
% 2.20/1.34  Reduction            : 0.08
% 2.20/1.34  Demodulation         : 0.06
% 2.20/1.34  BG Simplification    : 0.02
% 2.20/1.34  Subsumption          : 0.03
% 2.20/1.34  Abstraction          : 0.02
% 2.20/1.34  MUC search           : 0.00
% 2.20/1.34  Cooper               : 0.00
% 2.20/1.34  Total                : 0.60
% 2.20/1.34  Index Insertion      : 0.00
% 2.20/1.34  Index Deletion       : 0.00
% 2.20/1.34  Index Matching       : 0.00
% 2.20/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
