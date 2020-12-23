%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:43 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   36 (  41 expanded)
%              Number of leaves         :   25 (  28 expanded)
%              Depth                    :    5
%              Number of atoms          :   32 (  40 expanded)
%              Number of equality atoms :   24 (  32 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_44,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_46,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_46,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_48,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_88,plain,(
    ! [A_55,B_56] :
      ( r2_hidden(A_55,B_56)
      | k4_xboole_0(k1_tarski(A_55),B_56) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_92,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_88])).

tff(c_28,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_30,plain,(
    ! [A_11,B_12] : k1_enumset1(A_11,A_11,B_12) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_151,plain,(
    ! [E_70,C_71,B_72,A_73] :
      ( E_70 = C_71
      | E_70 = B_72
      | E_70 = A_73
      | ~ r2_hidden(E_70,k1_enumset1(A_73,B_72,C_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_170,plain,(
    ! [E_74,B_75,A_76] :
      ( E_74 = B_75
      | E_74 = A_76
      | E_74 = A_76
      | ~ r2_hidden(E_74,k2_tarski(A_76,B_75)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_151])).

tff(c_193,plain,(
    ! [E_82,A_83] :
      ( E_82 = A_83
      | E_82 = A_83
      | E_82 = A_83
      | ~ r2_hidden(E_82,k1_tarski(A_83)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_170])).

tff(c_196,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_92,c_193])).

tff(c_203,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_46,c_46,c_196])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:59:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.30  
% 2.03/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.31  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.03/1.31  
% 2.03/1.31  %Foreground sorts:
% 2.03/1.31  
% 2.03/1.31  
% 2.03/1.31  %Background operators:
% 2.03/1.31  
% 2.03/1.31  
% 2.03/1.31  %Foreground operators:
% 2.03/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.03/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.03/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.03/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.03/1.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.03/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.03/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.03/1.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.03/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.03/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.03/1.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.03/1.31  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.03/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.03/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.03/1.31  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.03/1.31  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.03/1.31  
% 2.03/1.31  tff(f_65, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 2.03/1.31  tff(f_60, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 2.03/1.31  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.03/1.31  tff(f_46, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.03/1.31  tff(f_42, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.03/1.31  tff(c_46, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.03/1.31  tff(c_48, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.03/1.31  tff(c_88, plain, (![A_55, B_56]: (r2_hidden(A_55, B_56) | k4_xboole_0(k1_tarski(A_55), B_56)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.03/1.31  tff(c_92, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_88])).
% 2.03/1.31  tff(c_28, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.03/1.31  tff(c_30, plain, (![A_11, B_12]: (k1_enumset1(A_11, A_11, B_12)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.03/1.31  tff(c_151, plain, (![E_70, C_71, B_72, A_73]: (E_70=C_71 | E_70=B_72 | E_70=A_73 | ~r2_hidden(E_70, k1_enumset1(A_73, B_72, C_71)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.03/1.31  tff(c_170, plain, (![E_74, B_75, A_76]: (E_74=B_75 | E_74=A_76 | E_74=A_76 | ~r2_hidden(E_74, k2_tarski(A_76, B_75)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_151])).
% 2.03/1.31  tff(c_193, plain, (![E_82, A_83]: (E_82=A_83 | E_82=A_83 | E_82=A_83 | ~r2_hidden(E_82, k1_tarski(A_83)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_170])).
% 2.03/1.31  tff(c_196, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_92, c_193])).
% 2.03/1.31  tff(c_203, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_46, c_46, c_196])).
% 2.03/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.31  
% 2.03/1.31  Inference rules
% 2.03/1.31  ----------------------
% 2.03/1.31  #Ref     : 0
% 2.03/1.31  #Sup     : 34
% 2.03/1.31  #Fact    : 0
% 2.03/1.31  #Define  : 0
% 2.03/1.31  #Split   : 0
% 2.03/1.31  #Chain   : 0
% 2.03/1.31  #Close   : 0
% 2.03/1.31  
% 2.03/1.31  Ordering : KBO
% 2.03/1.31  
% 2.03/1.31  Simplification rules
% 2.03/1.31  ----------------------
% 2.03/1.31  #Subsume      : 0
% 2.03/1.31  #Demod        : 4
% 2.03/1.31  #Tautology    : 26
% 2.03/1.31  #SimpNegUnit  : 1
% 2.03/1.31  #BackRed      : 0
% 2.03/1.31  
% 2.03/1.31  #Partial instantiations: 0
% 2.03/1.31  #Strategies tried      : 1
% 2.03/1.31  
% 2.03/1.31  Timing (in seconds)
% 2.03/1.31  ----------------------
% 2.03/1.32  Preprocessing        : 0.36
% 2.03/1.32  Parsing              : 0.19
% 2.03/1.32  CNF conversion       : 0.02
% 2.03/1.32  Main loop            : 0.18
% 2.03/1.32  Inferencing          : 0.06
% 2.03/1.32  Reduction            : 0.06
% 2.03/1.32  Demodulation         : 0.04
% 2.03/1.32  BG Simplification    : 0.02
% 2.03/1.32  Subsumption          : 0.03
% 2.03/1.32  Abstraction          : 0.01
% 2.03/1.32  MUC search           : 0.00
% 2.03/1.32  Cooper               : 0.00
% 2.03/1.32  Total                : 0.57
% 2.03/1.32  Index Insertion      : 0.00
% 2.03/1.32  Index Deletion       : 0.00
% 2.03/1.32  Index Matching       : 0.00
% 2.03/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
