%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:12 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   42 (  43 expanded)
%              Number of leaves         :   27 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 (  35 expanded)
%              Number of equality atoms :   14 (  15 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
          & A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_44,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_61,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_63,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_52,plain,(
    r1_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_53,plain,(
    r1_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52])).

tff(c_67,plain,(
    ! [A_42] :
      ( ~ r1_xboole_0(A_42,A_42)
      | k1_xboole_0 = A_42 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_74,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_53,c_67])).

tff(c_36,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_105,plain,(
    ! [A_58,B_59] : k1_enumset1(A_58,A_58,B_59) = k2_tarski(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_84,plain,(
    ! [E_45,A_46,C_47] : r2_hidden(E_45,k1_enumset1(A_46,E_45,C_47)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_88,plain,(
    ! [A_46,E_45,C_47] : ~ v1_xboole_0(k1_enumset1(A_46,E_45,C_47)) ),
    inference(resolution,[status(thm)],[c_84,c_2])).

tff(c_134,plain,(
    ! [A_63,B_64] : ~ v1_xboole_0(k2_tarski(A_63,B_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_88])).

tff(c_137,plain,(
    ! [A_65] : ~ v1_xboole_0(k1_tarski(A_65)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_134])).

tff(c_139,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_137])).

tff(c_142,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_139])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:00:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.27  
% 2.01/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.27  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.01/1.27  
% 2.01/1.27  %Foreground sorts:
% 2.01/1.27  
% 2.01/1.27  
% 2.01/1.27  %Background operators:
% 2.01/1.27  
% 2.01/1.27  
% 2.01/1.27  %Foreground operators:
% 2.01/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.01/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.01/1.27  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.01/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.01/1.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.01/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.01/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.01/1.27  tff('#skF_5', type, '#skF_5': $i).
% 2.01/1.27  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.01/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.01/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.01/1.27  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.01/1.27  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.01/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.01/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.27  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.01/1.27  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.01/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.01/1.27  
% 2.01/1.28  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.01/1.28  tff(f_79, negated_conjecture, ~(![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 2.01/1.28  tff(f_44, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.01/1.28  tff(f_61, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.01/1.28  tff(f_63, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.01/1.28  tff(f_59, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.01/1.28  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.01/1.28  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.01/1.28  tff(c_50, plain, ('#skF_5'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.01/1.28  tff(c_52, plain, (r1_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.01/1.28  tff(c_53, plain, (r1_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52])).
% 2.01/1.28  tff(c_67, plain, (![A_42]: (~r1_xboole_0(A_42, A_42) | k1_xboole_0=A_42)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.01/1.28  tff(c_74, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_53, c_67])).
% 2.01/1.28  tff(c_36, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.01/1.28  tff(c_105, plain, (![A_58, B_59]: (k1_enumset1(A_58, A_58, B_59)=k2_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.01/1.28  tff(c_84, plain, (![E_45, A_46, C_47]: (r2_hidden(E_45, k1_enumset1(A_46, E_45, C_47)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.01/1.28  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.01/1.28  tff(c_88, plain, (![A_46, E_45, C_47]: (~v1_xboole_0(k1_enumset1(A_46, E_45, C_47)))), inference(resolution, [status(thm)], [c_84, c_2])).
% 2.01/1.28  tff(c_134, plain, (![A_63, B_64]: (~v1_xboole_0(k2_tarski(A_63, B_64)))), inference(superposition, [status(thm), theory('equality')], [c_105, c_88])).
% 2.01/1.28  tff(c_137, plain, (![A_65]: (~v1_xboole_0(k1_tarski(A_65)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_134])).
% 2.01/1.28  tff(c_139, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_74, c_137])).
% 2.01/1.28  tff(c_142, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_139])).
% 2.01/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.28  
% 2.01/1.28  Inference rules
% 2.01/1.28  ----------------------
% 2.01/1.28  #Ref     : 0
% 2.01/1.28  #Sup     : 22
% 2.01/1.28  #Fact    : 0
% 2.01/1.28  #Define  : 0
% 2.01/1.28  #Split   : 0
% 2.01/1.28  #Chain   : 0
% 2.01/1.28  #Close   : 0
% 2.01/1.28  
% 2.01/1.28  Ordering : KBO
% 2.01/1.28  
% 2.01/1.28  Simplification rules
% 2.01/1.28  ----------------------
% 2.01/1.28  #Subsume      : 2
% 2.01/1.28  #Demod        : 5
% 2.01/1.28  #Tautology    : 13
% 2.01/1.28  #SimpNegUnit  : 0
% 2.01/1.28  #BackRed      : 1
% 2.01/1.28  
% 2.01/1.28  #Partial instantiations: 0
% 2.01/1.28  #Strategies tried      : 1
% 2.01/1.28  
% 2.01/1.28  Timing (in seconds)
% 2.01/1.28  ----------------------
% 2.01/1.28  Preprocessing        : 0.35
% 2.01/1.28  Parsing              : 0.18
% 2.01/1.28  CNF conversion       : 0.03
% 2.01/1.28  Main loop            : 0.13
% 2.01/1.28  Inferencing          : 0.04
% 2.01/1.28  Reduction            : 0.04
% 2.01/1.28  Demodulation         : 0.03
% 2.01/1.28  BG Simplification    : 0.02
% 2.01/1.28  Subsumption          : 0.03
% 2.01/1.28  Abstraction          : 0.01
% 2.01/1.28  MUC search           : 0.00
% 2.01/1.28  Cooper               : 0.00
% 2.01/1.28  Total                : 0.50
% 2.01/1.28  Index Insertion      : 0.00
% 2.01/1.28  Index Deletion       : 0.00
% 2.01/1.28  Index Matching       : 0.00
% 2.01/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
