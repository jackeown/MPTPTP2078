%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:35 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   48 (  48 expanded)
%              Number of leaves         :   31 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   39 (  39 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(f_51,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_49,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_16,plain,(
    ! [A_10] : r1_xboole_0(A_10,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_214,plain,(
    ! [A_56,B_57,C_58] :
      ( ~ r1_xboole_0(A_56,B_57)
      | ~ r2_hidden(C_58,k3_xboole_0(A_56,B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_217,plain,(
    ! [A_8,C_58] :
      ( ~ r1_xboole_0(A_8,k1_xboole_0)
      | ~ r2_hidden(C_58,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_214])).

tff(c_219,plain,(
    ! [C_58] : ~ r2_hidden(C_58,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_217])).

tff(c_14,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_50,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_66,plain,(
    ! [A_37,B_38] : r1_tarski(A_37,k2_xboole_0(A_37,B_38)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_69,plain,(
    r1_tarski(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_66])).

tff(c_135,plain,(
    ! [B_51,A_52] :
      ( B_51 = A_52
      | ~ r1_tarski(B_51,A_52)
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_139,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_69,c_135])).

tff(c_149,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_139])).

tff(c_72,plain,(
    ! [A_43] : k2_tarski(A_43,A_43) = k1_tarski(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_26,plain,(
    ! [D_20,B_16] : r2_hidden(D_20,k2_tarski(D_20,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_78,plain,(
    ! [A_43] : r2_hidden(A_43,k1_tarski(A_43)) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_26])).

tff(c_168,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_78])).

tff(c_221,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_219,c_168])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:05:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.22  
% 1.87/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.22  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.87/1.22  
% 1.87/1.22  %Foreground sorts:
% 1.87/1.22  
% 1.87/1.22  
% 1.87/1.22  %Background operators:
% 1.87/1.22  
% 1.87/1.22  
% 1.87/1.22  %Foreground operators:
% 1.87/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.87/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.87/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.87/1.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.87/1.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.87/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.87/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.87/1.22  tff('#skF_5', type, '#skF_5': $i).
% 1.87/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.87/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.87/1.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.87/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.22  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.87/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.87/1.22  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.87/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.87/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.87/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.87/1.22  
% 2.09/1.23  tff(f_51, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.09/1.23  tff(f_47, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.09/1.23  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.09/1.23  tff(f_49, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.09/1.23  tff(f_78, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.09/1.23  tff(f_53, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.09/1.23  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.09/1.23  tff(f_66, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.09/1.23  tff(f_64, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.09/1.23  tff(c_16, plain, (![A_10]: (r1_xboole_0(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.09/1.23  tff(c_12, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.09/1.23  tff(c_214, plain, (![A_56, B_57, C_58]: (~r1_xboole_0(A_56, B_57) | ~r2_hidden(C_58, k3_xboole_0(A_56, B_57)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.09/1.23  tff(c_217, plain, (![A_8, C_58]: (~r1_xboole_0(A_8, k1_xboole_0) | ~r2_hidden(C_58, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_214])).
% 2.09/1.23  tff(c_219, plain, (![C_58]: (~r2_hidden(C_58, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_217])).
% 2.09/1.23  tff(c_14, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.09/1.23  tff(c_50, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.09/1.23  tff(c_66, plain, (![A_37, B_38]: (r1_tarski(A_37, k2_xboole_0(A_37, B_38)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.09/1.23  tff(c_69, plain, (r1_tarski(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_50, c_66])).
% 2.09/1.23  tff(c_135, plain, (![B_51, A_52]: (B_51=A_52 | ~r1_tarski(B_51, A_52) | ~r1_tarski(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.09/1.23  tff(c_139, plain, (k1_tarski('#skF_4')=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_69, c_135])).
% 2.09/1.23  tff(c_149, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14, c_139])).
% 2.09/1.23  tff(c_72, plain, (![A_43]: (k2_tarski(A_43, A_43)=k1_tarski(A_43))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.09/1.23  tff(c_26, plain, (![D_20, B_16]: (r2_hidden(D_20, k2_tarski(D_20, B_16)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.09/1.23  tff(c_78, plain, (![A_43]: (r2_hidden(A_43, k1_tarski(A_43)))), inference(superposition, [status(thm), theory('equality')], [c_72, c_26])).
% 2.09/1.23  tff(c_168, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_149, c_78])).
% 2.09/1.23  tff(c_221, plain, $false, inference(negUnitSimplification, [status(thm)], [c_219, c_168])).
% 2.09/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.23  
% 2.09/1.23  Inference rules
% 2.09/1.23  ----------------------
% 2.09/1.23  #Ref     : 0
% 2.09/1.23  #Sup     : 42
% 2.09/1.23  #Fact    : 0
% 2.09/1.23  #Define  : 0
% 2.09/1.23  #Split   : 1
% 2.09/1.23  #Chain   : 0
% 2.09/1.23  #Close   : 0
% 2.09/1.23  
% 2.09/1.23  Ordering : KBO
% 2.09/1.23  
% 2.09/1.23  Simplification rules
% 2.09/1.23  ----------------------
% 2.09/1.23  #Subsume      : 0
% 2.09/1.23  #Demod        : 11
% 2.09/1.23  #Tautology    : 31
% 2.09/1.23  #SimpNegUnit  : 1
% 2.09/1.23  #BackRed      : 3
% 2.09/1.23  
% 2.09/1.23  #Partial instantiations: 0
% 2.09/1.23  #Strategies tried      : 1
% 2.09/1.23  
% 2.09/1.23  Timing (in seconds)
% 2.09/1.23  ----------------------
% 2.09/1.24  Preprocessing        : 0.32
% 2.09/1.24  Parsing              : 0.17
% 2.09/1.24  CNF conversion       : 0.02
% 2.09/1.24  Main loop            : 0.15
% 2.09/1.24  Inferencing          : 0.05
% 2.09/1.24  Reduction            : 0.05
% 2.09/1.24  Demodulation         : 0.04
% 2.09/1.24  BG Simplification    : 0.01
% 2.09/1.24  Subsumption          : 0.03
% 2.09/1.24  Abstraction          : 0.01
% 2.09/1.24  MUC search           : 0.00
% 2.09/1.24  Cooper               : 0.00
% 2.09/1.24  Total                : 0.49
% 2.09/1.24  Index Insertion      : 0.00
% 2.09/1.24  Index Deletion       : 0.00
% 2.09/1.24  Index Matching       : 0.00
% 2.09/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
