%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:13 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   34 (  35 expanded)
%              Number of leaves         :   21 (  22 expanded)
%              Depth                    :    4
%              Number of atoms          :   29 (  31 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_58,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_60,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
          & A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_32,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_67,plain,(
    ! [A_32,B_33] : k1_enumset1(A_32,A_32,B_33) = k2_tarski(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12,plain,(
    ! [E_14,A_8,C_10] : r2_hidden(E_14,k1_enumset1(A_8,E_14,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_85,plain,(
    ! [A_34,B_35] : r2_hidden(A_34,k2_tarski(A_34,B_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_12])).

tff(c_88,plain,(
    ! [A_15] : r2_hidden(A_15,k1_tarski(A_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_85])).

tff(c_38,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_40,plain,(
    r1_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_41,plain,(
    r1_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_89,plain,(
    ! [A_36,B_37,C_38] :
      ( ~ r1_xboole_0(A_36,B_37)
      | ~ r2_hidden(C_38,k3_xboole_0(A_36,B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_100,plain,(
    ! [A_42,C_43] :
      ( ~ r1_xboole_0(A_42,A_42)
      | ~ r2_hidden(C_43,A_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_89])).

tff(c_104,plain,(
    ! [C_44] : ~ r2_hidden(C_44,k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_41,c_100])).

tff(c_109,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_88,c_104])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n012.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 11:24:37 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.14  
% 1.91/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.14  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.91/1.14  
% 1.91/1.14  %Foreground sorts:
% 1.91/1.14  
% 1.91/1.14  
% 1.91/1.14  %Background operators:
% 1.91/1.14  
% 1.91/1.14  
% 1.91/1.14  %Foreground operators:
% 1.91/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.91/1.14  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.91/1.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.91/1.14  tff('#skF_5', type, '#skF_5': $i).
% 1.91/1.14  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 1.91/1.14  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.91/1.14  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.91/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.91/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.91/1.14  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 1.91/1.14  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.91/1.14  
% 1.91/1.15  tff(f_58, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.91/1.15  tff(f_60, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.91/1.15  tff(f_56, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 1.91/1.15  tff(f_68, negated_conjecture, ~(![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 1.91/1.15  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 1.91/1.15  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.91/1.15  tff(c_32, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.91/1.15  tff(c_67, plain, (![A_32, B_33]: (k1_enumset1(A_32, A_32, B_33)=k2_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.91/1.15  tff(c_12, plain, (![E_14, A_8, C_10]: (r2_hidden(E_14, k1_enumset1(A_8, E_14, C_10)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.91/1.15  tff(c_85, plain, (![A_34, B_35]: (r2_hidden(A_34, k2_tarski(A_34, B_35)))), inference(superposition, [status(thm), theory('equality')], [c_67, c_12])).
% 1.91/1.15  tff(c_88, plain, (![A_15]: (r2_hidden(A_15, k1_tarski(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_85])).
% 1.91/1.15  tff(c_38, plain, ('#skF_5'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.91/1.15  tff(c_40, plain, (r1_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.91/1.15  tff(c_41, plain, (r1_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40])).
% 1.91/1.15  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.91/1.15  tff(c_89, plain, (![A_36, B_37, C_38]: (~r1_xboole_0(A_36, B_37) | ~r2_hidden(C_38, k3_xboole_0(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.91/1.15  tff(c_100, plain, (![A_42, C_43]: (~r1_xboole_0(A_42, A_42) | ~r2_hidden(C_43, A_42))), inference(superposition, [status(thm), theory('equality')], [c_2, c_89])).
% 1.91/1.15  tff(c_104, plain, (![C_44]: (~r2_hidden(C_44, k1_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_41, c_100])).
% 1.91/1.15  tff(c_109, plain, $false, inference(resolution, [status(thm)], [c_88, c_104])).
% 1.91/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.15  
% 1.91/1.15  Inference rules
% 1.91/1.15  ----------------------
% 1.91/1.15  #Ref     : 0
% 1.91/1.15  #Sup     : 16
% 1.91/1.15  #Fact    : 0
% 1.91/1.15  #Define  : 0
% 1.91/1.15  #Split   : 0
% 1.91/1.15  #Chain   : 0
% 1.91/1.15  #Close   : 0
% 1.91/1.15  
% 1.91/1.15  Ordering : KBO
% 1.91/1.15  
% 1.91/1.15  Simplification rules
% 1.91/1.15  ----------------------
% 1.91/1.15  #Subsume      : 0
% 1.91/1.15  #Demod        : 3
% 1.91/1.15  #Tautology    : 10
% 1.91/1.15  #SimpNegUnit  : 0
% 1.91/1.15  #BackRed      : 0
% 1.91/1.15  
% 1.91/1.15  #Partial instantiations: 0
% 1.91/1.15  #Strategies tried      : 1
% 1.91/1.15  
% 1.91/1.15  Timing (in seconds)
% 1.91/1.15  ----------------------
% 1.91/1.15  Preprocessing        : 0.31
% 1.91/1.15  Parsing              : 0.16
% 1.91/1.15  CNF conversion       : 0.02
% 1.91/1.15  Main loop            : 0.11
% 1.91/1.15  Inferencing          : 0.03
% 1.91/1.15  Reduction            : 0.04
% 1.91/1.15  Demodulation         : 0.03
% 1.91/1.15  BG Simplification    : 0.02
% 1.91/1.15  Subsumption          : 0.02
% 1.91/1.15  Abstraction          : 0.01
% 1.91/1.15  MUC search           : 0.00
% 1.91/1.15  Cooper               : 0.00
% 1.91/1.15  Total                : 0.45
% 1.91/1.15  Index Insertion      : 0.00
% 1.91/1.15  Index Deletion       : 0.00
% 1.91/1.16  Index Matching       : 0.00
% 1.91/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
