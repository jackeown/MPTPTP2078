%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:13 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   48 (  57 expanded)
%              Number of leaves         :   27 (  31 expanded)
%              Depth                    :    5
%              Number of atoms          :   44 (  59 expanded)
%              Number of equality atoms :   19 (  25 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
          & A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_74,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_76,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_10,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_127,plain,(
    ! [A_51,B_52] : k4_xboole_0(A_51,k4_xboole_0(A_51,B_52)) = k3_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_8] : k4_xboole_0(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_154,plain,(
    ! [B_53] : k3_xboole_0(k1_xboole_0,B_53) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_8])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_159,plain,(
    ! [B_53,C_5] :
      ( ~ r1_xboole_0(k1_xboole_0,B_53)
      | ~ r2_hidden(C_5,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_4])).

tff(c_175,plain,(
    ! [C_5] : ~ r2_hidden(C_5,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_159])).

tff(c_48,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_50,plain,(
    r1_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_51,plain,(
    r1_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50])).

tff(c_74,plain,(
    ! [A_31] :
      ( ~ r1_xboole_0(A_31,A_31)
      | k1_xboole_0 = A_31 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_82,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_51,c_74])).

tff(c_40,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_94,plain,(
    ! [A_41,B_42] : k1_enumset1(A_41,A_41,B_42) = k2_tarski(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_20,plain,(
    ! [E_17,A_11,C_13] : r2_hidden(E_17,k1_enumset1(A_11,E_17,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_112,plain,(
    ! [A_43,B_44] : r2_hidden(A_43,k2_tarski(A_43,B_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_20])).

tff(c_116,plain,(
    ! [A_45] : r2_hidden(A_45,k1_tarski(A_45)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_112])).

tff(c_119,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_116])).

tff(c_177,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_175,c_119])).

tff(c_179,plain,(
    ! [B_57] : ~ r1_xboole_0(k1_xboole_0,B_57) ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_184,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_10,c_179])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:58:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.24  
% 1.93/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.25  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.93/1.25  
% 1.93/1.25  %Foreground sorts:
% 1.93/1.25  
% 1.93/1.25  
% 1.93/1.25  %Background operators:
% 1.93/1.25  
% 1.93/1.25  
% 1.93/1.25  %Foreground operators:
% 1.93/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.93/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.93/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.93/1.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.93/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.93/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.93/1.25  tff('#skF_5', type, '#skF_5': $i).
% 1.93/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 1.93/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.93/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.93/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.25  tff('#skF_4', type, '#skF_4': $i).
% 1.93/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.93/1.25  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 1.93/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.93/1.25  
% 1.93/1.26  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.93/1.26  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.93/1.26  tff(f_43, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 1.93/1.26  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.93/1.26  tff(f_86, negated_conjecture, ~(![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 1.93/1.26  tff(f_57, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 1.93/1.26  tff(f_74, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.93/1.26  tff(f_76, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.93/1.26  tff(f_72, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 1.93/1.26  tff(c_10, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.93/1.26  tff(c_127, plain, (![A_51, B_52]: (k4_xboole_0(A_51, k4_xboole_0(A_51, B_52))=k3_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.93/1.26  tff(c_8, plain, (![A_8]: (k4_xboole_0(k1_xboole_0, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.93/1.26  tff(c_154, plain, (![B_53]: (k3_xboole_0(k1_xboole_0, B_53)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_127, c_8])).
% 1.93/1.26  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.93/1.26  tff(c_159, plain, (![B_53, C_5]: (~r1_xboole_0(k1_xboole_0, B_53) | ~r2_hidden(C_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_154, c_4])).
% 1.93/1.26  tff(c_175, plain, (![C_5]: (~r2_hidden(C_5, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_159])).
% 1.93/1.26  tff(c_48, plain, ('#skF_5'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.93/1.26  tff(c_50, plain, (r1_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.93/1.26  tff(c_51, plain, (r1_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50])).
% 1.93/1.26  tff(c_74, plain, (![A_31]: (~r1_xboole_0(A_31, A_31) | k1_xboole_0=A_31)), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.93/1.26  tff(c_82, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_51, c_74])).
% 1.93/1.26  tff(c_40, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.93/1.26  tff(c_94, plain, (![A_41, B_42]: (k1_enumset1(A_41, A_41, B_42)=k2_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.93/1.26  tff(c_20, plain, (![E_17, A_11, C_13]: (r2_hidden(E_17, k1_enumset1(A_11, E_17, C_13)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.93/1.26  tff(c_112, plain, (![A_43, B_44]: (r2_hidden(A_43, k2_tarski(A_43, B_44)))), inference(superposition, [status(thm), theory('equality')], [c_94, c_20])).
% 1.93/1.26  tff(c_116, plain, (![A_45]: (r2_hidden(A_45, k1_tarski(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_112])).
% 1.93/1.26  tff(c_119, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_82, c_116])).
% 1.93/1.26  tff(c_177, plain, $false, inference(negUnitSimplification, [status(thm)], [c_175, c_119])).
% 1.93/1.26  tff(c_179, plain, (![B_57]: (~r1_xboole_0(k1_xboole_0, B_57))), inference(splitRight, [status(thm)], [c_159])).
% 1.93/1.26  tff(c_184, plain, $false, inference(resolution, [status(thm)], [c_10, c_179])).
% 1.93/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.26  
% 1.93/1.26  Inference rules
% 1.93/1.26  ----------------------
% 1.93/1.26  #Ref     : 0
% 1.93/1.26  #Sup     : 31
% 1.93/1.26  #Fact    : 0
% 1.93/1.26  #Define  : 0
% 1.93/1.26  #Split   : 1
% 1.93/1.26  #Chain   : 0
% 1.93/1.26  #Close   : 0
% 1.93/1.26  
% 1.93/1.26  Ordering : KBO
% 1.93/1.26  
% 1.93/1.26  Simplification rules
% 1.93/1.26  ----------------------
% 1.93/1.26  #Subsume      : 0
% 1.93/1.26  #Demod        : 10
% 1.93/1.26  #Tautology    : 23
% 1.93/1.26  #SimpNegUnit  : 1
% 1.93/1.26  #BackRed      : 2
% 1.93/1.26  
% 1.93/1.26  #Partial instantiations: 0
% 1.93/1.26  #Strategies tried      : 1
% 1.93/1.26  
% 1.93/1.26  Timing (in seconds)
% 1.93/1.26  ----------------------
% 1.93/1.26  Preprocessing        : 0.31
% 1.93/1.26  Parsing              : 0.16
% 1.93/1.26  CNF conversion       : 0.02
% 1.93/1.26  Main loop            : 0.13
% 1.93/1.26  Inferencing          : 0.04
% 1.93/1.26  Reduction            : 0.05
% 1.93/1.26  Demodulation         : 0.03
% 1.93/1.26  BG Simplification    : 0.01
% 1.93/1.26  Subsumption          : 0.02
% 1.93/1.26  Abstraction          : 0.01
% 1.93/1.26  MUC search           : 0.00
% 1.93/1.26  Cooper               : 0.00
% 1.93/1.26  Total                : 0.47
% 1.93/1.26  Index Insertion      : 0.00
% 1.93/1.26  Index Deletion       : 0.00
% 1.93/1.26  Index Matching       : 0.00
% 1.93/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
