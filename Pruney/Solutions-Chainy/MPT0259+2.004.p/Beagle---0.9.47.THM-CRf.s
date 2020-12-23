%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:08 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   32 (  33 expanded)
%              Number of leaves         :   21 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   27 (  29 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r1_xboole_0(k1_tarski(A),B)
          & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_zfmisc_1)).

tff(f_54,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_50,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_44,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_62,plain,(
    ! [D_24,B_25] : r2_hidden(D_24,k2_tarski(D_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_65,plain,(
    ! [A_17] : r2_hidden(A_17,k1_tarski(A_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_62])).

tff(c_52,plain,(
    r1_xboole_0(k1_tarski('#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_84,plain,(
    ! [A_33,B_34] :
      ( k4_xboole_0(A_33,B_34) = A_33
      | ~ r1_xboole_0(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_96,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_84])).

tff(c_122,plain,(
    ! [D_39,B_40,A_41] :
      ( ~ r2_hidden(D_39,B_40)
      | ~ r2_hidden(D_39,k4_xboole_0(A_41,B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_136,plain,(
    ! [D_45] :
      ( ~ r2_hidden(D_45,'#skF_6')
      | ~ r2_hidden(D_45,k1_tarski('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_122])).

tff(c_140,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_65,c_136])).

tff(c_144,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_140])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:53:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.34  
% 2.01/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.35  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 2.01/1.35  
% 2.01/1.35  %Foreground sorts:
% 2.01/1.35  
% 2.01/1.35  
% 2.01/1.35  %Background operators:
% 2.01/1.35  
% 2.01/1.35  
% 2.01/1.35  %Foreground operators:
% 2.01/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.01/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.01/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.01/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.01/1.35  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.01/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.01/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.01/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.01/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.01/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.01/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.01/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.01/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.01/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.35  
% 2.01/1.35  tff(f_64, negated_conjecture, ~(![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_zfmisc_1)).
% 2.01/1.35  tff(f_54, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.01/1.35  tff(f_52, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.01/1.35  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.01/1.35  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.01/1.35  tff(c_50, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.01/1.35  tff(c_44, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.01/1.35  tff(c_62, plain, (![D_24, B_25]: (r2_hidden(D_24, k2_tarski(D_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.01/1.35  tff(c_65, plain, (![A_17]: (r2_hidden(A_17, k1_tarski(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_62])).
% 2.01/1.35  tff(c_52, plain, (r1_xboole_0(k1_tarski('#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.01/1.35  tff(c_84, plain, (![A_33, B_34]: (k4_xboole_0(A_33, B_34)=A_33 | ~r1_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.01/1.35  tff(c_96, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_52, c_84])).
% 2.01/1.35  tff(c_122, plain, (![D_39, B_40, A_41]: (~r2_hidden(D_39, B_40) | ~r2_hidden(D_39, k4_xboole_0(A_41, B_40)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.01/1.35  tff(c_136, plain, (![D_45]: (~r2_hidden(D_45, '#skF_6') | ~r2_hidden(D_45, k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_96, c_122])).
% 2.01/1.35  tff(c_140, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_65, c_136])).
% 2.01/1.35  tff(c_144, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_140])).
% 2.01/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.35  
% 2.01/1.35  Inference rules
% 2.01/1.35  ----------------------
% 2.01/1.35  #Ref     : 0
% 2.01/1.35  #Sup     : 23
% 2.01/1.35  #Fact    : 0
% 2.01/1.35  #Define  : 0
% 2.01/1.35  #Split   : 0
% 2.01/1.35  #Chain   : 0
% 2.01/1.35  #Close   : 0
% 2.01/1.35  
% 2.01/1.35  Ordering : KBO
% 2.01/1.35  
% 2.01/1.35  Simplification rules
% 2.01/1.35  ----------------------
% 2.01/1.35  #Subsume      : 1
% 2.01/1.35  #Demod        : 3
% 2.01/1.35  #Tautology    : 13
% 2.01/1.35  #SimpNegUnit  : 0
% 2.01/1.35  #BackRed      : 0
% 2.01/1.35  
% 2.01/1.35  #Partial instantiations: 0
% 2.01/1.35  #Strategies tried      : 1
% 2.01/1.35  
% 2.01/1.35  Timing (in seconds)
% 2.01/1.35  ----------------------
% 2.01/1.36  Preprocessing        : 0.38
% 2.01/1.36  Parsing              : 0.19
% 2.01/1.36  CNF conversion       : 0.03
% 2.01/1.36  Main loop            : 0.13
% 2.01/1.36  Inferencing          : 0.04
% 2.01/1.36  Reduction            : 0.05
% 2.01/1.36  Demodulation         : 0.03
% 2.01/1.36  BG Simplification    : 0.02
% 2.01/1.36  Subsumption          : 0.03
% 2.01/1.36  Abstraction          : 0.01
% 2.01/1.36  MUC search           : 0.00
% 2.01/1.36  Cooper               : 0.00
% 2.01/1.36  Total                : 0.53
% 2.01/1.36  Index Insertion      : 0.00
% 2.01/1.36  Index Deletion       : 0.00
% 2.01/1.36  Index Matching       : 0.00
% 2.01/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
