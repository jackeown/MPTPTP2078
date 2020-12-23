%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:41 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   38 (  39 expanded)
%              Number of leaves         :   23 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 (  35 expanded)
%              Number of equality atoms :   26 (  28 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_50,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( A != B
       => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( A != B
     => k4_xboole_0(k2_tarski(A,B),k1_tarski(B)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(c_91,plain,(
    ! [A_36,B_37] : k1_enumset1(A_36,A_36,B_37) = k2_tarski(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    ! [E_13,A_7,B_8] : r2_hidden(E_13,k1_enumset1(A_7,B_8,E_13)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_97,plain,(
    ! [B_37,A_36] : r2_hidden(B_37,k2_tarski(A_36,B_37)) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_10])).

tff(c_38,plain,(
    ! [A_20,B_21] :
      ( k2_xboole_0(k1_tarski(A_20),B_21) = B_21
      | ~ r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_44,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_173,plain,(
    ! [A_52,B_53] :
      ( k4_xboole_0(k2_tarski(A_52,B_53),k1_tarski(B_53)) = k1_tarski(A_52)
      | B_53 = A_52 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_294,plain,(
    ! [B_72,A_73] :
      ( k5_xboole_0(k1_tarski(B_72),k1_tarski(A_73)) = k2_xboole_0(k1_tarski(B_72),k2_tarski(A_73,B_72))
      | B_72 = A_73 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_4])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k2_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_45,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k2_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_42])).

tff(c_306,plain,
    ( k2_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_3')) != k2_tarski('#skF_4','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_45])).

tff(c_330,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_3')) != k2_tarski('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_306])).

tff(c_338,plain,(
    ~ r2_hidden('#skF_3',k2_tarski('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_330])).

tff(c_342,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_338])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:44:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.27  
% 2.09/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.27  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.09/1.27  
% 2.09/1.27  %Foreground sorts:
% 2.09/1.27  
% 2.09/1.27  
% 2.09/1.27  %Background operators:
% 2.09/1.27  
% 2.09/1.27  
% 2.09/1.27  %Foreground operators:
% 2.09/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.09/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.09/1.27  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.09/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.09/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.09/1.27  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.09/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.09/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.09/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.09/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.09/1.27  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.09/1.27  
% 2.09/1.28  tff(f_50, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.09/1.28  tff(f_46, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.09/1.28  tff(f_56, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 2.09/1.28  tff(f_67, negated_conjecture, ~(![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 2.09/1.28  tff(f_61, axiom, (![A, B]: (~(A = B) => (k4_xboole_0(k2_tarski(A, B), k1_tarski(B)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_zfmisc_1)).
% 2.09/1.28  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.09/1.28  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.09/1.28  tff(c_91, plain, (![A_36, B_37]: (k1_enumset1(A_36, A_36, B_37)=k2_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.09/1.28  tff(c_10, plain, (![E_13, A_7, B_8]: (r2_hidden(E_13, k1_enumset1(A_7, B_8, E_13)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.09/1.28  tff(c_97, plain, (![B_37, A_36]: (r2_hidden(B_37, k2_tarski(A_36, B_37)))), inference(superposition, [status(thm), theory('equality')], [c_91, c_10])).
% 2.09/1.28  tff(c_38, plain, (![A_20, B_21]: (k2_xboole_0(k1_tarski(A_20), B_21)=B_21 | ~r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.09/1.28  tff(c_44, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.09/1.28  tff(c_173, plain, (![A_52, B_53]: (k4_xboole_0(k2_tarski(A_52, B_53), k1_tarski(B_53))=k1_tarski(A_52) | B_53=A_52)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.09/1.28  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.09/1.28  tff(c_294, plain, (![B_72, A_73]: (k5_xboole_0(k1_tarski(B_72), k1_tarski(A_73))=k2_xboole_0(k1_tarski(B_72), k2_tarski(A_73, B_72)) | B_72=A_73)), inference(superposition, [status(thm), theory('equality')], [c_173, c_4])).
% 2.09/1.28  tff(c_6, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.09/1.28  tff(c_42, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k2_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.09/1.28  tff(c_45, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k2_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_42])).
% 2.09/1.28  tff(c_306, plain, (k2_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_3'))!=k2_tarski('#skF_4', '#skF_3') | '#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_294, c_45])).
% 2.09/1.28  tff(c_330, plain, (k2_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_3'))!=k2_tarski('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_44, c_306])).
% 2.09/1.28  tff(c_338, plain, (~r2_hidden('#skF_3', k2_tarski('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_330])).
% 2.09/1.28  tff(c_342, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_97, c_338])).
% 2.09/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.28  
% 2.09/1.28  Inference rules
% 2.09/1.28  ----------------------
% 2.09/1.28  #Ref     : 0
% 2.09/1.28  #Sup     : 69
% 2.09/1.28  #Fact    : 0
% 2.09/1.28  #Define  : 0
% 2.09/1.28  #Split   : 0
% 2.09/1.28  #Chain   : 0
% 2.09/1.28  #Close   : 0
% 2.09/1.28  
% 2.09/1.28  Ordering : KBO
% 2.09/1.28  
% 2.09/1.28  Simplification rules
% 2.09/1.28  ----------------------
% 2.09/1.28  #Subsume      : 7
% 2.09/1.28  #Demod        : 10
% 2.09/1.28  #Tautology    : 47
% 2.09/1.28  #SimpNegUnit  : 1
% 2.09/1.28  #BackRed      : 0
% 2.09/1.28  
% 2.09/1.28  #Partial instantiations: 0
% 2.09/1.28  #Strategies tried      : 1
% 2.09/1.28  
% 2.09/1.28  Timing (in seconds)
% 2.09/1.28  ----------------------
% 2.09/1.29  Preprocessing        : 0.31
% 2.09/1.29  Parsing              : 0.16
% 2.09/1.29  CNF conversion       : 0.02
% 2.09/1.29  Main loop            : 0.20
% 2.09/1.29  Inferencing          : 0.07
% 2.09/1.29  Reduction            : 0.07
% 2.09/1.29  Demodulation         : 0.05
% 2.09/1.29  BG Simplification    : 0.01
% 2.09/1.29  Subsumption          : 0.04
% 2.09/1.29  Abstraction          : 0.01
% 2.09/1.29  MUC search           : 0.00
% 2.09/1.29  Cooper               : 0.00
% 2.09/1.29  Total                : 0.53
% 2.09/1.29  Index Insertion      : 0.00
% 2.09/1.29  Index Deletion       : 0.00
% 2.09/1.29  Index Matching       : 0.00
% 2.09/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
