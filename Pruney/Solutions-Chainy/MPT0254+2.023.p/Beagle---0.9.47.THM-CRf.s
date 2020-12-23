%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:23 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   44 (  44 expanded)
%              Number of leaves         :   29 (  29 expanded)
%              Depth                    :    5
%              Number of atoms          :   33 (  33 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_53,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_47,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_68,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_16,plain,(
    ! [A_14] : r1_xboole_0(A_14,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_209,plain,(
    ! [A_57,B_58,C_59] :
      ( ~ r1_xboole_0(A_57,B_58)
      | ~ r2_hidden(C_59,k3_xboole_0(A_57,B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_212,plain,(
    ! [A_6,C_59] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_59,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_209])).

tff(c_214,plain,(
    ! [C_59] : ~ r2_hidden(C_59,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_212])).

tff(c_50,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_18,plain,(
    ! [A_15,B_16] : r1_tarski(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_72,plain,(
    r1_tarski(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_18])).

tff(c_10,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_80,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_72,c_10])).

tff(c_40,plain,(
    ! [A_25] : k2_tarski(A_25,A_25) = k1_tarski(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_109,plain,(
    ! [D_44,A_45] : r2_hidden(D_44,k2_tarski(A_45,D_44)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_113,plain,(
    ! [A_46] : r2_hidden(A_46,k1_tarski(A_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_109])).

tff(c_116,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_113])).

tff(c_216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_116])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:33:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.26  
% 2.04/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.26  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.04/1.26  
% 2.04/1.26  %Foreground sorts:
% 2.04/1.26  
% 2.04/1.26  
% 2.04/1.26  %Background operators:
% 2.04/1.26  
% 2.04/1.26  
% 2.04/1.26  %Foreground operators:
% 2.04/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.04/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.04/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.04/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.04/1.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.04/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.04/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.04/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.04/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.04/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.04/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.04/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.04/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.26  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.04/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.04/1.26  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.04/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.04/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.04/1.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.04/1.26  
% 2.04/1.27  tff(f_53, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.04/1.27  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.04/1.27  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.04/1.27  tff(f_80, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.04/1.27  tff(f_55, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.04/1.27  tff(f_47, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.04/1.27  tff(f_68, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.04/1.27  tff(f_66, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.04/1.27  tff(c_16, plain, (![A_14]: (r1_xboole_0(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.04/1.27  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.04/1.27  tff(c_209, plain, (![A_57, B_58, C_59]: (~r1_xboole_0(A_57, B_58) | ~r2_hidden(C_59, k3_xboole_0(A_57, B_58)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.04/1.27  tff(c_212, plain, (![A_6, C_59]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_59, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_209])).
% 2.04/1.27  tff(c_214, plain, (![C_59]: (~r2_hidden(C_59, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_212])).
% 2.04/1.27  tff(c_50, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.04/1.27  tff(c_18, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.04/1.27  tff(c_72, plain, (r1_tarski(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_50, c_18])).
% 2.04/1.27  tff(c_10, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.04/1.27  tff(c_80, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_72, c_10])).
% 2.04/1.27  tff(c_40, plain, (![A_25]: (k2_tarski(A_25, A_25)=k1_tarski(A_25))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.04/1.27  tff(c_109, plain, (![D_44, A_45]: (r2_hidden(D_44, k2_tarski(A_45, D_44)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.04/1.27  tff(c_113, plain, (![A_46]: (r2_hidden(A_46, k1_tarski(A_46)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_109])).
% 2.04/1.27  tff(c_116, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_80, c_113])).
% 2.04/1.27  tff(c_216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_214, c_116])).
% 2.04/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.27  
% 2.04/1.27  Inference rules
% 2.04/1.27  ----------------------
% 2.04/1.27  #Ref     : 0
% 2.04/1.27  #Sup     : 42
% 2.04/1.27  #Fact    : 0
% 2.04/1.27  #Define  : 0
% 2.04/1.27  #Split   : 0
% 2.04/1.27  #Chain   : 0
% 2.04/1.27  #Close   : 0
% 2.04/1.27  
% 2.04/1.27  Ordering : KBO
% 2.04/1.27  
% 2.04/1.27  Simplification rules
% 2.04/1.27  ----------------------
% 2.04/1.27  #Subsume      : 0
% 2.04/1.27  #Demod        : 10
% 2.04/1.27  #Tautology    : 34
% 2.04/1.27  #SimpNegUnit  : 1
% 2.04/1.27  #BackRed      : 3
% 2.04/1.27  
% 2.04/1.27  #Partial instantiations: 0
% 2.04/1.27  #Strategies tried      : 1
% 2.04/1.27  
% 2.04/1.27  Timing (in seconds)
% 2.04/1.27  ----------------------
% 2.04/1.27  Preprocessing        : 0.32
% 2.04/1.27  Parsing              : 0.17
% 2.04/1.28  CNF conversion       : 0.02
% 2.04/1.28  Main loop            : 0.14
% 2.04/1.28  Inferencing          : 0.04
% 2.04/1.28  Reduction            : 0.05
% 2.04/1.28  Demodulation         : 0.04
% 2.04/1.28  BG Simplification    : 0.01
% 2.04/1.28  Subsumption          : 0.02
% 2.04/1.28  Abstraction          : 0.01
% 2.04/1.28  MUC search           : 0.00
% 2.04/1.28  Cooper               : 0.00
% 2.04/1.28  Total                : 0.48
% 2.04/1.28  Index Insertion      : 0.00
% 2.04/1.28  Index Deletion       : 0.00
% 2.04/1.28  Index Matching       : 0.00
% 2.04/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
