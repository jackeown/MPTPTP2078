%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:13 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   37 (  38 expanded)
%              Number of leaves         :   22 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   36 (  38 expanded)
%              Number of equality atoms :   13 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_57,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_62,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => r2_xboole_0(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_55,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

tff(c_14,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_23,plain,(
    ! [A_18,B_19] :
      ( k2_xboole_0(A_18,B_19) = B_19
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_27,plain,(
    ! [A_14] : k2_xboole_0(k1_xboole_0,A_14) = A_14 ),
    inference(resolution,[status(thm)],[c_14,c_23])).

tff(c_20,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_16,plain,(
    ! [A_15] :
      ( r2_xboole_0(k1_xboole_0,A_15)
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_38,plain,(
    ! [A_24,B_25] :
      ( r2_hidden('#skF_2'(A_24,B_25),B_25)
      | ~ r2_xboole_0(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_62,plain,(
    ! [A_31,B_32,A_33] :
      ( ~ r1_xboole_0(A_31,B_32)
      | ~ r2_xboole_0(A_33,k3_xboole_0(A_31,B_32)) ) ),
    inference(resolution,[status(thm)],[c_38,c_4])).

tff(c_68,plain,(
    ! [A_34,B_35] :
      ( ~ r1_xboole_0(A_34,B_35)
      | k3_xboole_0(A_34,B_35) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_62])).

tff(c_72,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_68])).

tff(c_98,plain,(
    ! [A_37,B_38,C_39] : k2_xboole_0(k3_xboole_0(A_37,B_38),k3_xboole_0(A_37,C_39)) = k3_xboole_0(A_37,k2_xboole_0(B_38,C_39)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_107,plain,(
    ! [C_39] : k3_xboole_0('#skF_3',k2_xboole_0('#skF_4',C_39)) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_3',C_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_98])).

tff(c_113,plain,(
    ! [C_39] : k3_xboole_0('#skF_3',k2_xboole_0('#skF_4',C_39)) = k3_xboole_0('#skF_3',C_39) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_107])).

tff(c_18,plain,(
    k3_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) != k3_xboole_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_122,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:48:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.16  
% 1.79/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.17  %$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.79/1.17  
% 1.79/1.17  %Foreground sorts:
% 1.79/1.17  
% 1.79/1.17  
% 1.79/1.17  %Background operators:
% 1.79/1.17  
% 1.79/1.17  
% 1.79/1.17  %Foreground operators:
% 1.79/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.79/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.79/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.79/1.17  tff('#skF_5', type, '#skF_5': $i).
% 1.79/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.79/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.79/1.17  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.79/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.79/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.79/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.79/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.79/1.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.79/1.17  
% 1.79/1.18  tff(f_57, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.79/1.18  tff(f_53, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.79/1.18  tff(f_67, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_xboole_1)).
% 1.79/1.18  tff(f_62, axiom, (![A]: (~(A = k1_xboole_0) => r2_xboole_0(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_xboole_1)).
% 1.79/1.18  tff(f_49, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 1.79/1.18  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.79/1.18  tff(f_55, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_xboole_1)).
% 1.79/1.18  tff(c_14, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.79/1.18  tff(c_23, plain, (![A_18, B_19]: (k2_xboole_0(A_18, B_19)=B_19 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.79/1.18  tff(c_27, plain, (![A_14]: (k2_xboole_0(k1_xboole_0, A_14)=A_14)), inference(resolution, [status(thm)], [c_14, c_23])).
% 1.79/1.18  tff(c_20, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.79/1.18  tff(c_16, plain, (![A_15]: (r2_xboole_0(k1_xboole_0, A_15) | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.79/1.18  tff(c_38, plain, (![A_24, B_25]: (r2_hidden('#skF_2'(A_24, B_25), B_25) | ~r2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.79/1.18  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.79/1.18  tff(c_62, plain, (![A_31, B_32, A_33]: (~r1_xboole_0(A_31, B_32) | ~r2_xboole_0(A_33, k3_xboole_0(A_31, B_32)))), inference(resolution, [status(thm)], [c_38, c_4])).
% 1.79/1.18  tff(c_68, plain, (![A_34, B_35]: (~r1_xboole_0(A_34, B_35) | k3_xboole_0(A_34, B_35)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_62])).
% 1.79/1.18  tff(c_72, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_68])).
% 1.79/1.18  tff(c_98, plain, (![A_37, B_38, C_39]: (k2_xboole_0(k3_xboole_0(A_37, B_38), k3_xboole_0(A_37, C_39))=k3_xboole_0(A_37, k2_xboole_0(B_38, C_39)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.79/1.18  tff(c_107, plain, (![C_39]: (k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', C_39))=k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_3', C_39)))), inference(superposition, [status(thm), theory('equality')], [c_72, c_98])).
% 1.79/1.18  tff(c_113, plain, (![C_39]: (k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', C_39))=k3_xboole_0('#skF_3', C_39))), inference(demodulation, [status(thm), theory('equality')], [c_27, c_107])).
% 1.79/1.18  tff(c_18, plain, (k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))!=k3_xboole_0('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.79/1.18  tff(c_122, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_113, c_18])).
% 1.79/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.18  
% 1.79/1.18  Inference rules
% 1.79/1.18  ----------------------
% 1.79/1.18  #Ref     : 0
% 1.79/1.18  #Sup     : 20
% 1.79/1.18  #Fact    : 0
% 1.79/1.18  #Define  : 0
% 1.79/1.18  #Split   : 0
% 1.79/1.18  #Chain   : 0
% 1.79/1.18  #Close   : 0
% 1.79/1.18  
% 1.79/1.18  Ordering : KBO
% 1.79/1.18  
% 1.79/1.18  Simplification rules
% 1.79/1.18  ----------------------
% 1.79/1.18  #Subsume      : 1
% 1.79/1.18  #Demod        : 5
% 1.79/1.18  #Tautology    : 10
% 1.79/1.18  #SimpNegUnit  : 0
% 1.79/1.18  #BackRed      : 1
% 1.79/1.18  
% 1.79/1.18  #Partial instantiations: 0
% 1.79/1.18  #Strategies tried      : 1
% 1.79/1.18  
% 1.79/1.18  Timing (in seconds)
% 1.79/1.18  ----------------------
% 1.79/1.18  Preprocessing        : 0.26
% 1.79/1.18  Parsing              : 0.15
% 1.79/1.18  CNF conversion       : 0.02
% 1.79/1.18  Main loop            : 0.12
% 1.79/1.18  Inferencing          : 0.06
% 1.79/1.18  Reduction            : 0.03
% 1.79/1.18  Demodulation         : 0.02
% 1.79/1.18  BG Simplification    : 0.01
% 1.79/1.18  Subsumption          : 0.02
% 1.79/1.18  Abstraction          : 0.00
% 1.79/1.18  MUC search           : 0.00
% 1.79/1.18  Cooper               : 0.00
% 1.79/1.18  Total                : 0.40
% 1.79/1.18  Index Insertion      : 0.00
% 1.79/1.18  Index Deletion       : 0.00
% 1.79/1.18  Index Matching       : 0.00
% 1.79/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
