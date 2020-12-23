%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:02 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   40 (  47 expanded)
%              Number of leaves         :   25 (  30 expanded)
%              Depth                    :    5
%              Number of atoms          :   34 (  48 expanded)
%              Number of equality atoms :   26 (  39 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_56,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_54,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_52,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_118,plain,(
    ! [A_74,B_75] : k2_xboole_0(k1_tarski(A_74),k1_tarski(B_75)) = k2_tarski(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_54,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_124,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_54])).

tff(c_71,plain,(
    ! [A_63,B_64] : k1_enumset1(A_63,A_63,B_64) = k2_tarski(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12,plain,(
    ! [E_16,A_10,B_11] : r2_hidden(E_16,k1_enumset1(A_10,B_11,E_16)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_77,plain,(
    ! [B_64,A_63] : r2_hidden(B_64,k2_tarski(A_63,B_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_12])).

tff(c_139,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_77])).

tff(c_38,plain,(
    ! [A_25] : k2_tarski(A_25,A_25) = k1_tarski(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_40,plain,(
    ! [A_26,B_27] : k1_enumset1(A_26,A_26,B_27) = k2_tarski(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_270,plain,(
    ! [E_90,C_91,B_92,A_93] :
      ( E_90 = C_91
      | E_90 = B_92
      | E_90 = A_93
      | ~ r2_hidden(E_90,k1_enumset1(A_93,B_92,C_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_289,plain,(
    ! [E_94,B_95,A_96] :
      ( E_94 = B_95
      | E_94 = A_96
      | E_94 = A_96
      | ~ r2_hidden(E_94,k2_tarski(A_96,B_95)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_270])).

tff(c_331,plain,(
    ! [E_103,A_104] :
      ( E_103 = A_104
      | E_103 = A_104
      | E_103 = A_104
      | ~ r2_hidden(E_103,k1_tarski(A_104)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_289])).

tff(c_334,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_139,c_331])).

tff(c_341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_52,c_52,c_334])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:30:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.39  
% 2.37/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.39  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.37/1.39  
% 2.37/1.39  %Foreground sorts:
% 2.37/1.39  
% 2.37/1.39  
% 2.37/1.39  %Background operators:
% 2.37/1.39  
% 2.37/1.39  
% 2.37/1.39  %Foreground operators:
% 2.37/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.37/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.37/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.37/1.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.37/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.37/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.37/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.37/1.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.37/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.37/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.37/1.39  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.37/1.39  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.37/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.37/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.37/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.37/1.39  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.37/1.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.37/1.39  
% 2.37/1.40  tff(f_71, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 2.37/1.40  tff(f_50, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.37/1.40  tff(f_56, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.37/1.40  tff(f_48, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.37/1.40  tff(f_54, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.37/1.40  tff(c_52, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.37/1.40  tff(c_118, plain, (![A_74, B_75]: (k2_xboole_0(k1_tarski(A_74), k1_tarski(B_75))=k2_tarski(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.37/1.40  tff(c_54, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.37/1.40  tff(c_124, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_118, c_54])).
% 2.37/1.40  tff(c_71, plain, (![A_63, B_64]: (k1_enumset1(A_63, A_63, B_64)=k2_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.37/1.40  tff(c_12, plain, (![E_16, A_10, B_11]: (r2_hidden(E_16, k1_enumset1(A_10, B_11, E_16)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.37/1.40  tff(c_77, plain, (![B_64, A_63]: (r2_hidden(B_64, k2_tarski(A_63, B_64)))), inference(superposition, [status(thm), theory('equality')], [c_71, c_12])).
% 2.37/1.40  tff(c_139, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_124, c_77])).
% 2.37/1.40  tff(c_38, plain, (![A_25]: (k2_tarski(A_25, A_25)=k1_tarski(A_25))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.37/1.40  tff(c_40, plain, (![A_26, B_27]: (k1_enumset1(A_26, A_26, B_27)=k2_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.37/1.40  tff(c_270, plain, (![E_90, C_91, B_92, A_93]: (E_90=C_91 | E_90=B_92 | E_90=A_93 | ~r2_hidden(E_90, k1_enumset1(A_93, B_92, C_91)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.37/1.40  tff(c_289, plain, (![E_94, B_95, A_96]: (E_94=B_95 | E_94=A_96 | E_94=A_96 | ~r2_hidden(E_94, k2_tarski(A_96, B_95)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_270])).
% 2.37/1.40  tff(c_331, plain, (![E_103, A_104]: (E_103=A_104 | E_103=A_104 | E_103=A_104 | ~r2_hidden(E_103, k1_tarski(A_104)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_289])).
% 2.37/1.40  tff(c_334, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_139, c_331])).
% 2.37/1.40  tff(c_341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_52, c_52, c_334])).
% 2.37/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.40  
% 2.37/1.40  Inference rules
% 2.37/1.40  ----------------------
% 2.37/1.40  #Ref     : 0
% 2.37/1.40  #Sup     : 69
% 2.37/1.40  #Fact    : 0
% 2.37/1.40  #Define  : 0
% 2.37/1.40  #Split   : 0
% 2.37/1.40  #Chain   : 0
% 2.37/1.40  #Close   : 0
% 2.37/1.40  
% 2.37/1.40  Ordering : KBO
% 2.37/1.40  
% 2.37/1.40  Simplification rules
% 2.37/1.40  ----------------------
% 2.37/1.40  #Subsume      : 0
% 2.37/1.40  #Demod        : 13
% 2.37/1.40  #Tautology    : 41
% 2.37/1.40  #SimpNegUnit  : 3
% 2.37/1.40  #BackRed      : 0
% 2.37/1.40  
% 2.37/1.40  #Partial instantiations: 0
% 2.37/1.40  #Strategies tried      : 1
% 2.37/1.40  
% 2.37/1.40  Timing (in seconds)
% 2.37/1.40  ----------------------
% 2.37/1.40  Preprocessing        : 0.35
% 2.37/1.40  Parsing              : 0.19
% 2.37/1.40  CNF conversion       : 0.02
% 2.37/1.40  Main loop            : 0.21
% 2.37/1.40  Inferencing          : 0.08
% 2.37/1.40  Reduction            : 0.07
% 2.37/1.40  Demodulation         : 0.06
% 2.37/1.40  BG Simplification    : 0.02
% 2.37/1.40  Subsumption          : 0.04
% 2.37/1.40  Abstraction          : 0.01
% 2.37/1.40  MUC search           : 0.00
% 2.37/1.40  Cooper               : 0.00
% 2.37/1.40  Total                : 0.59
% 2.37/1.40  Index Insertion      : 0.00
% 2.37/1.40  Index Deletion       : 0.00
% 2.37/1.40  Index Matching       : 0.00
% 2.37/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
