%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:21 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   45 (  45 expanded)
%              Number of leaves         :   28 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  36 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_58,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_12,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_65,plain,(
    ! [A_39,B_40] : r1_xboole_0(k4_xboole_0(A_39,B_40),B_40) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_68,plain,(
    ! [A_6] : r1_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_65])).

tff(c_153,plain,(
    ! [A_54,B_55] :
      ( ~ r2_hidden(A_54,B_55)
      | ~ r1_xboole_0(k1_tarski(A_54),B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_158,plain,(
    ! [A_54] : ~ r2_hidden(A_54,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_68,c_153])).

tff(c_10,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_52,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_91,plain,(
    ! [A_47,B_48] : r1_tarski(A_47,k2_xboole_0(A_47,B_48)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_94,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_91])).

tff(c_258,plain,(
    ! [B_70,A_71] :
      ( B_70 = A_71
      | ~ r1_tarski(B_70,A_71)
      | ~ r1_tarski(A_71,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_262,plain,
    ( k1_tarski('#skF_3') = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_94,c_258])).

tff(c_272,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_262])).

tff(c_76,plain,(
    ! [A_46] : k2_tarski(A_46,A_46) = k1_tarski(A_46) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_26,plain,(
    ! [D_21,B_17] : r2_hidden(D_21,k2_tarski(D_21,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_82,plain,(
    ! [A_46] : r2_hidden(A_46,k1_tarski(A_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_26])).

tff(c_297,plain,(
    r2_hidden('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_82])).

tff(c_304,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_158,c_297])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:53:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.23  
% 2.11/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.23  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.11/1.23  
% 2.11/1.23  %Foreground sorts:
% 2.11/1.23  
% 2.11/1.23  
% 2.11/1.23  %Background operators:
% 2.11/1.23  
% 2.11/1.23  
% 2.11/1.23  %Foreground operators:
% 2.11/1.23  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.11/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.11/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.11/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.11/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.11/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.11/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.11/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.11/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.11/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.11/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.11/1.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.11/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.23  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.11/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.11/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.11/1.23  
% 2.14/1.24  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.14/1.24  tff(f_43, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.14/1.24  tff(f_69, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.14/1.24  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.14/1.24  tff(f_75, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.14/1.24  tff(f_45, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.14/1.24  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.14/1.24  tff(f_58, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.14/1.24  tff(f_56, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.14/1.24  tff(c_12, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.14/1.24  tff(c_65, plain, (![A_39, B_40]: (r1_xboole_0(k4_xboole_0(A_39, B_40), B_40))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.14/1.24  tff(c_68, plain, (![A_6]: (r1_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_65])).
% 2.14/1.24  tff(c_153, plain, (![A_54, B_55]: (~r2_hidden(A_54, B_55) | ~r1_xboole_0(k1_tarski(A_54), B_55))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.14/1.24  tff(c_158, plain, (![A_54]: (~r2_hidden(A_54, k1_xboole_0))), inference(resolution, [status(thm)], [c_68, c_153])).
% 2.14/1.24  tff(c_10, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.14/1.24  tff(c_52, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.14/1.24  tff(c_91, plain, (![A_47, B_48]: (r1_tarski(A_47, k2_xboole_0(A_47, B_48)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.14/1.24  tff(c_94, plain, (r1_tarski(k1_tarski('#skF_3'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_52, c_91])).
% 2.14/1.24  tff(c_258, plain, (![B_70, A_71]: (B_70=A_71 | ~r1_tarski(B_70, A_71) | ~r1_tarski(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.14/1.24  tff(c_262, plain, (k1_tarski('#skF_3')=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_94, c_258])).
% 2.14/1.24  tff(c_272, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10, c_262])).
% 2.14/1.24  tff(c_76, plain, (![A_46]: (k2_tarski(A_46, A_46)=k1_tarski(A_46))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.14/1.24  tff(c_26, plain, (![D_21, B_17]: (r2_hidden(D_21, k2_tarski(D_21, B_17)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.14/1.24  tff(c_82, plain, (![A_46]: (r2_hidden(A_46, k1_tarski(A_46)))), inference(superposition, [status(thm), theory('equality')], [c_76, c_26])).
% 2.14/1.24  tff(c_297, plain, (r2_hidden('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_272, c_82])).
% 2.14/1.24  tff(c_304, plain, $false, inference(negUnitSimplification, [status(thm)], [c_158, c_297])).
% 2.14/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.24  
% 2.14/1.24  Inference rules
% 2.14/1.24  ----------------------
% 2.14/1.24  #Ref     : 0
% 2.14/1.24  #Sup     : 61
% 2.14/1.24  #Fact    : 0
% 2.14/1.24  #Define  : 0
% 2.14/1.24  #Split   : 0
% 2.14/1.24  #Chain   : 0
% 2.14/1.24  #Close   : 0
% 2.14/1.24  
% 2.14/1.24  Ordering : KBO
% 2.14/1.24  
% 2.14/1.24  Simplification rules
% 2.14/1.24  ----------------------
% 2.14/1.24  #Subsume      : 1
% 2.14/1.24  #Demod        : 19
% 2.14/1.24  #Tautology    : 39
% 2.14/1.24  #SimpNegUnit  : 1
% 2.14/1.24  #BackRed      : 2
% 2.14/1.24  
% 2.14/1.24  #Partial instantiations: 0
% 2.14/1.24  #Strategies tried      : 1
% 2.14/1.24  
% 2.14/1.24  Timing (in seconds)
% 2.14/1.24  ----------------------
% 2.14/1.24  Preprocessing        : 0.30
% 2.14/1.24  Parsing              : 0.15
% 2.14/1.24  CNF conversion       : 0.02
% 2.14/1.24  Main loop            : 0.17
% 2.14/1.24  Inferencing          : 0.06
% 2.14/1.24  Reduction            : 0.06
% 2.14/1.24  Demodulation         : 0.05
% 2.14/1.24  BG Simplification    : 0.01
% 2.14/1.24  Subsumption          : 0.03
% 2.14/1.24  Abstraction          : 0.01
% 2.14/1.24  MUC search           : 0.00
% 2.14/1.24  Cooper               : 0.00
% 2.14/1.24  Total                : 0.49
% 2.14/1.24  Index Insertion      : 0.00
% 2.14/1.24  Index Deletion       : 0.00
% 2.14/1.24  Index Matching       : 0.00
% 2.14/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
