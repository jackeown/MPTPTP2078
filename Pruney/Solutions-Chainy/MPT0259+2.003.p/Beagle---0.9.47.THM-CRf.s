%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:08 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   30 (  31 expanded)
%              Number of leaves         :   19 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   29 (  31 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r1_xboole_0(k1_tarski(A),B)
          & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_zfmisc_1)).

tff(f_60,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_62,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_38,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_32,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_53,plain,(
    ! [A_29,B_30] : k1_enumset1(A_29,A_29,B_30) = k2_tarski(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_12,plain,(
    ! [E_12,A_6,C_8] : r2_hidden(E_12,k1_enumset1(A_6,E_12,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_71,plain,(
    ! [A_31,B_32] : r2_hidden(A_31,k2_tarski(A_31,B_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_12])).

tff(c_74,plain,(
    ! [A_13] : r2_hidden(A_13,k1_tarski(A_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_71])).

tff(c_40,plain,(
    r1_xboole_0(k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_84,plain,(
    ! [A_40,B_41,C_42] :
      ( ~ r1_xboole_0(A_40,B_41)
      | ~ r2_hidden(C_42,B_41)
      | ~ r2_hidden(C_42,A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_88,plain,(
    ! [C_43] :
      ( ~ r2_hidden(C_43,'#skF_5')
      | ~ r2_hidden(C_43,k1_tarski('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_40,c_84])).

tff(c_100,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_88])).

tff(c_106,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_100])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n010.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 17:22:59 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.15  
% 1.66/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.15  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.66/1.15  
% 1.66/1.15  %Foreground sorts:
% 1.66/1.15  
% 1.66/1.15  
% 1.66/1.15  %Background operators:
% 1.66/1.15  
% 1.66/1.15  
% 1.66/1.15  %Foreground operators:
% 1.66/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.66/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.66/1.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.66/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.66/1.15  tff('#skF_5', type, '#skF_5': $i).
% 1.66/1.15  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 1.66/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.66/1.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.66/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.15  tff('#skF_4', type, '#skF_4': $i).
% 1.66/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.15  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 1.66/1.15  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.66/1.15  
% 1.66/1.16  tff(f_70, negated_conjecture, ~(![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_zfmisc_1)).
% 1.66/1.16  tff(f_60, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.66/1.16  tff(f_62, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.66/1.16  tff(f_58, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 1.66/1.16  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.66/1.16  tff(c_38, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.66/1.16  tff(c_32, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.66/1.16  tff(c_53, plain, (![A_29, B_30]: (k1_enumset1(A_29, A_29, B_30)=k2_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.66/1.16  tff(c_12, plain, (![E_12, A_6, C_8]: (r2_hidden(E_12, k1_enumset1(A_6, E_12, C_8)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.66/1.16  tff(c_71, plain, (![A_31, B_32]: (r2_hidden(A_31, k2_tarski(A_31, B_32)))), inference(superposition, [status(thm), theory('equality')], [c_53, c_12])).
% 1.66/1.16  tff(c_74, plain, (![A_13]: (r2_hidden(A_13, k1_tarski(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_71])).
% 1.66/1.16  tff(c_40, plain, (r1_xboole_0(k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.66/1.16  tff(c_84, plain, (![A_40, B_41, C_42]: (~r1_xboole_0(A_40, B_41) | ~r2_hidden(C_42, B_41) | ~r2_hidden(C_42, A_40))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.66/1.16  tff(c_88, plain, (![C_43]: (~r2_hidden(C_43, '#skF_5') | ~r2_hidden(C_43, k1_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_40, c_84])).
% 1.66/1.16  tff(c_100, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_74, c_88])).
% 1.66/1.16  tff(c_106, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_100])).
% 1.66/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.16  
% 1.66/1.16  Inference rules
% 1.66/1.16  ----------------------
% 1.66/1.16  #Ref     : 0
% 1.66/1.16  #Sup     : 13
% 1.66/1.16  #Fact    : 0
% 1.66/1.16  #Define  : 0
% 1.66/1.16  #Split   : 0
% 1.66/1.16  #Chain   : 0
% 1.66/1.16  #Close   : 0
% 1.66/1.16  
% 1.66/1.16  Ordering : KBO
% 1.66/1.16  
% 1.66/1.16  Simplification rules
% 1.66/1.16  ----------------------
% 1.66/1.16  #Subsume      : 0
% 1.66/1.16  #Demod        : 3
% 1.66/1.16  #Tautology    : 6
% 1.66/1.16  #SimpNegUnit  : 0
% 1.66/1.16  #BackRed      : 0
% 1.66/1.16  
% 1.66/1.16  #Partial instantiations: 0
% 1.66/1.16  #Strategies tried      : 1
% 1.66/1.16  
% 1.66/1.16  Timing (in seconds)
% 1.66/1.16  ----------------------
% 1.66/1.16  Preprocessing        : 0.30
% 1.66/1.16  Parsing              : 0.15
% 1.66/1.16  CNF conversion       : 0.02
% 1.66/1.16  Main loop            : 0.12
% 1.66/1.16  Inferencing          : 0.04
% 1.66/1.16  Reduction            : 0.04
% 1.66/1.16  Demodulation         : 0.03
% 1.66/1.16  BG Simplification    : 0.02
% 1.66/1.16  Subsumption          : 0.02
% 1.66/1.16  Abstraction          : 0.01
% 1.66/1.16  MUC search           : 0.00
% 1.66/1.16  Cooper               : 0.00
% 1.66/1.16  Total                : 0.44
% 1.66/1.16  Index Insertion      : 0.00
% 1.66/1.16  Index Deletion       : 0.00
% 1.66/1.16  Index Matching       : 0.00
% 1.66/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
