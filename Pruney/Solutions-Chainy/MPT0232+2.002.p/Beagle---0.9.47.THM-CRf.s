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
% DateTime   : Thu Dec  3 09:49:20 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   33 (  41 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   34 (  44 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_61,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_67,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => k2_tarski(A,B) = k1_tarski(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_91,plain,(
    ! [B_43,A_44] : k2_tarski(B_43,A_44) = k2_tarski(A_44,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_30,plain,(
    ! [A_28,B_29] : r1_tarski(k1_tarski(A_28),k2_tarski(A_28,B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_106,plain,(
    ! [A_44,B_43] : r1_tarski(k1_tarski(A_44),k2_tarski(B_43,A_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_30])).

tff(c_36,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_732,plain,(
    ! [A_89,C_90,B_91] :
      ( r1_tarski(A_89,C_90)
      | ~ r1_tarski(B_91,C_90)
      | ~ r1_tarski(A_89,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_781,plain,(
    ! [A_92] :
      ( r1_tarski(A_92,k1_tarski('#skF_3'))
      | ~ r1_tarski(A_92,k2_tarski('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_36,c_732])).

tff(c_803,plain,(
    r1_tarski(k1_tarski('#skF_2'),k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_106,c_781])).

tff(c_32,plain,(
    ! [B_31,A_30] :
      ( B_31 = A_30
      | ~ r1_tarski(k1_tarski(A_30),k1_tarski(B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_821,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_803,c_32])).

tff(c_34,plain,(
    k2_tarski('#skF_1','#skF_2') != k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_185,plain,(
    ! [B_52,A_53] :
      ( B_52 = A_53
      | ~ r1_tarski(B_52,A_53)
      | ~ r1_tarski(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_193,plain,
    ( k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_3')
    | ~ r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_185])).

tff(c_205,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_193])).

tff(c_826,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_821,c_205])).

tff(c_832,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_826])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:42:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.38  
% 2.54/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.39  %$ r1_tarski > k2_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.54/1.39  
% 2.54/1.39  %Foreground sorts:
% 2.54/1.39  
% 2.54/1.39  
% 2.54/1.39  %Background operators:
% 2.54/1.39  
% 2.54/1.39  
% 2.54/1.39  %Foreground operators:
% 2.54/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.54/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.54/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.54/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.54/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.54/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.54/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.54/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.54/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.54/1.39  
% 2.76/1.39  tff(f_61, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.76/1.39  tff(f_67, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 2.76/1.39  tff(f_76, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (k2_tarski(A, B) = k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_zfmisc_1)).
% 2.76/1.39  tff(f_51, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.76/1.39  tff(f_71, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_zfmisc_1)).
% 2.76/1.39  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.76/1.39  tff(c_91, plain, (![B_43, A_44]: (k2_tarski(B_43, A_44)=k2_tarski(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.76/1.39  tff(c_30, plain, (![A_28, B_29]: (r1_tarski(k1_tarski(A_28), k2_tarski(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.76/1.39  tff(c_106, plain, (![A_44, B_43]: (r1_tarski(k1_tarski(A_44), k2_tarski(B_43, A_44)))), inference(superposition, [status(thm), theory('equality')], [c_91, c_30])).
% 2.76/1.39  tff(c_36, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.76/1.39  tff(c_732, plain, (![A_89, C_90, B_91]: (r1_tarski(A_89, C_90) | ~r1_tarski(B_91, C_90) | ~r1_tarski(A_89, B_91))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.76/1.39  tff(c_781, plain, (![A_92]: (r1_tarski(A_92, k1_tarski('#skF_3')) | ~r1_tarski(A_92, k2_tarski('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_36, c_732])).
% 2.76/1.39  tff(c_803, plain, (r1_tarski(k1_tarski('#skF_2'), k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_106, c_781])).
% 2.76/1.39  tff(c_32, plain, (![B_31, A_30]: (B_31=A_30 | ~r1_tarski(k1_tarski(A_30), k1_tarski(B_31)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.76/1.39  tff(c_821, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_803, c_32])).
% 2.76/1.39  tff(c_34, plain, (k2_tarski('#skF_1', '#skF_2')!=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.76/1.39  tff(c_185, plain, (![B_52, A_53]: (B_52=A_53 | ~r1_tarski(B_52, A_53) | ~r1_tarski(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.76/1.39  tff(c_193, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_3') | ~r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_185])).
% 2.76/1.39  tff(c_205, plain, (~r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_34, c_193])).
% 2.76/1.39  tff(c_826, plain, (~r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_821, c_205])).
% 2.76/1.39  tff(c_832, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_826])).
% 2.76/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.39  
% 2.76/1.39  Inference rules
% 2.76/1.39  ----------------------
% 2.76/1.39  #Ref     : 0
% 2.76/1.39  #Sup     : 197
% 2.76/1.39  #Fact    : 0
% 2.76/1.39  #Define  : 0
% 2.76/1.39  #Split   : 0
% 2.76/1.39  #Chain   : 0
% 2.76/1.39  #Close   : 0
% 2.76/1.39  
% 2.76/1.39  Ordering : KBO
% 2.76/1.39  
% 2.76/1.39  Simplification rules
% 2.76/1.39  ----------------------
% 2.76/1.40  #Subsume      : 1
% 2.76/1.40  #Demod        : 82
% 2.76/1.40  #Tautology    : 114
% 2.76/1.40  #SimpNegUnit  : 1
% 2.76/1.40  #BackRed      : 7
% 2.76/1.40  
% 2.76/1.40  #Partial instantiations: 0
% 2.76/1.40  #Strategies tried      : 1
% 2.76/1.40  
% 2.76/1.40  Timing (in seconds)
% 2.76/1.40  ----------------------
% 2.76/1.40  Preprocessing        : 0.31
% 2.76/1.40  Parsing              : 0.17
% 2.76/1.40  CNF conversion       : 0.02
% 2.76/1.40  Main loop            : 0.32
% 2.76/1.40  Inferencing          : 0.10
% 2.76/1.40  Reduction            : 0.13
% 2.76/1.40  Demodulation         : 0.10
% 2.76/1.40  BG Simplification    : 0.02
% 2.76/1.40  Subsumption          : 0.06
% 2.76/1.40  Abstraction          : 0.02
% 2.76/1.40  MUC search           : 0.00
% 2.76/1.40  Cooper               : 0.00
% 2.76/1.40  Total                : 0.66
% 2.76/1.40  Index Insertion      : 0.00
% 2.76/1.40  Index Deletion       : 0.00
% 2.76/1.40  Index Matching       : 0.00
% 2.76/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
