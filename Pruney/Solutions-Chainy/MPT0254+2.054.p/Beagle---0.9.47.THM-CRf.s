%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:26 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   39 (  39 expanded)
%              Number of leaves         :   26 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   27 (  27 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_34,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_46,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_61,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_46,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_77,plain,(
    ! [A_32,B_33] : r1_tarski(A_32,k2_xboole_0(A_32,B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_80,plain,(
    r1_tarski(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_77])).

tff(c_16,plain,(
    ! [A_11] :
      ( k1_xboole_0 = A_11
      | ~ r1_tarski(A_11,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_84,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_80,c_16])).

tff(c_40,plain,(
    ! [A_22] : k2_tarski(A_22,A_22) = k1_tarski(A_22) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_100,plain,(
    ! [D_34,A_35] : r2_hidden(D_34,k2_tarski(A_35,D_34)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_104,plain,(
    ! [A_36] : r2_hidden(A_36,k1_tarski(A_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_100])).

tff(c_107,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_104])).

tff(c_108,plain,(
    ! [B_37,A_38] :
      ( ~ r2_hidden(B_37,A_38)
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_111,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_107,c_108])).

tff(c_121,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_111])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n001.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 17:16:15 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.16  
% 1.72/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.17  %$ r2_hidden > r1_tarski > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 1.72/1.17  
% 1.72/1.17  %Foreground sorts:
% 1.72/1.17  
% 1.72/1.17  
% 1.72/1.17  %Background operators:
% 1.72/1.17  
% 1.72/1.17  
% 1.72/1.17  %Foreground operators:
% 1.72/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.72/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.72/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.72/1.17  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.72/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.72/1.17  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.72/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.72/1.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.72/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.72/1.17  tff('#skF_5', type, '#skF_5': $i).
% 1.72/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.72/1.17  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.72/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.72/1.17  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.72/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.72/1.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.72/1.17  
% 1.92/1.18  tff(f_34, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.92/1.18  tff(f_69, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.92/1.18  tff(f_48, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.92/1.18  tff(f_46, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.92/1.18  tff(f_61, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.92/1.18  tff(f_59, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.92/1.18  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.92/1.18  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.92/1.18  tff(c_46, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.92/1.18  tff(c_77, plain, (![A_32, B_33]: (r1_tarski(A_32, k2_xboole_0(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.92/1.18  tff(c_80, plain, (r1_tarski(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_46, c_77])).
% 1.92/1.18  tff(c_16, plain, (![A_11]: (k1_xboole_0=A_11 | ~r1_tarski(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.92/1.18  tff(c_84, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_80, c_16])).
% 1.92/1.18  tff(c_40, plain, (![A_22]: (k2_tarski(A_22, A_22)=k1_tarski(A_22))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.92/1.18  tff(c_100, plain, (![D_34, A_35]: (r2_hidden(D_34, k2_tarski(A_35, D_34)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.92/1.18  tff(c_104, plain, (![A_36]: (r2_hidden(A_36, k1_tarski(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_100])).
% 1.92/1.18  tff(c_107, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_84, c_104])).
% 1.92/1.18  tff(c_108, plain, (![B_37, A_38]: (~r2_hidden(B_37, A_38) | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.92/1.18  tff(c_111, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_107, c_108])).
% 1.92/1.18  tff(c_121, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_111])).
% 1.92/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.18  
% 1.92/1.18  Inference rules
% 1.92/1.18  ----------------------
% 1.92/1.18  #Ref     : 0
% 1.92/1.18  #Sup     : 19
% 1.92/1.18  #Fact    : 0
% 1.92/1.18  #Define  : 0
% 1.92/1.18  #Split   : 0
% 1.92/1.18  #Chain   : 0
% 1.92/1.18  #Close   : 0
% 1.92/1.18  
% 1.92/1.18  Ordering : KBO
% 1.92/1.18  
% 1.92/1.18  Simplification rules
% 1.92/1.18  ----------------------
% 1.92/1.18  #Subsume      : 0
% 1.92/1.18  #Demod        : 5
% 1.92/1.18  #Tautology    : 13
% 1.92/1.18  #SimpNegUnit  : 0
% 1.92/1.18  #BackRed      : 2
% 1.92/1.18  
% 1.92/1.18  #Partial instantiations: 0
% 1.92/1.18  #Strategies tried      : 1
% 1.92/1.18  
% 1.92/1.18  Timing (in seconds)
% 1.92/1.18  ----------------------
% 1.92/1.18  Preprocessing        : 0.32
% 1.92/1.18  Parsing              : 0.16
% 1.92/1.18  CNF conversion       : 0.02
% 1.92/1.18  Main loop            : 0.11
% 1.92/1.18  Inferencing          : 0.03
% 1.92/1.18  Reduction            : 0.04
% 1.92/1.18  Demodulation         : 0.03
% 1.92/1.18  BG Simplification    : 0.01
% 1.92/1.18  Subsumption          : 0.02
% 1.92/1.18  Abstraction          : 0.01
% 1.92/1.18  MUC search           : 0.00
% 1.92/1.18  Cooper               : 0.00
% 1.92/1.18  Total                : 0.45
% 1.92/1.18  Index Insertion      : 0.00
% 1.92/1.18  Index Deletion       : 0.00
% 1.92/1.18  Index Matching       : 0.00
% 1.92/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
