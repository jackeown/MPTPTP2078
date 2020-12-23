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
% DateTime   : Thu Dec  3 09:52:16 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   35 (  38 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  36 expanded)
%              Number of equality atoms :   13 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(k1_tarski(A),B)
        | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_82,plain,(
    ! [A_24,B_25] :
      ( r1_xboole_0(k1_tarski(A_24),B_25)
      | r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_38,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_86,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_38])).

tff(c_22,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_147,plain,(
    ! [A_47,B_48] :
      ( k4_xboole_0(k1_tarski(A_47),B_48) = k1_tarski(A_47)
      | r2_hidden(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_434,plain,(
    ! [A_68,B_69] :
      ( k3_xboole_0(k1_tarski(A_68),B_69) = k1_tarski(A_68)
      | r2_hidden(A_68,k4_xboole_0(k1_tarski(A_68),B_69)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_147])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_468,plain,(
    ! [A_70,B_71] :
      ( ~ r2_hidden(A_70,B_71)
      | k3_xboole_0(k1_tarski(A_70),B_71) = k1_tarski(A_70) ) ),
    inference(resolution,[status(thm)],[c_434,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_509,plain,(
    ! [B_72,A_73] :
      ( k3_xboole_0(B_72,k1_tarski(A_73)) = k1_tarski(A_73)
      | ~ r2_hidden(A_73,B_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_468,c_2])).

tff(c_36,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_39,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_3')) != k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_36])).

tff(c_535,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_509,c_39])).

tff(c_565,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_535])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:58:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.32  
% 2.37/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.32  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.37/1.32  
% 2.37/1.32  %Foreground sorts:
% 2.37/1.32  
% 2.37/1.32  
% 2.37/1.32  %Background operators:
% 2.37/1.32  
% 2.37/1.32  
% 2.37/1.32  %Foreground operators:
% 2.37/1.32  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.37/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.37/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.37/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.37/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.37/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.37/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.37/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.37/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.37/1.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.37/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.37/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.37/1.32  
% 2.37/1.33  tff(f_50, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.37/1.33  tff(f_60, negated_conjecture, ~(![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 2.37/1.33  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.37/1.33  tff(f_55, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 2.37/1.33  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.37/1.33  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.37/1.33  tff(c_82, plain, (![A_24, B_25]: (r1_xboole_0(k1_tarski(A_24), B_25) | r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.37/1.33  tff(c_38, plain, (~r1_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.37/1.33  tff(c_86, plain, (r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_82, c_38])).
% 2.37/1.33  tff(c_22, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.37/1.33  tff(c_147, plain, (![A_47, B_48]: (k4_xboole_0(k1_tarski(A_47), B_48)=k1_tarski(A_47) | r2_hidden(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.37/1.33  tff(c_434, plain, (![A_68, B_69]: (k3_xboole_0(k1_tarski(A_68), B_69)=k1_tarski(A_68) | r2_hidden(A_68, k4_xboole_0(k1_tarski(A_68), B_69)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_147])).
% 2.37/1.33  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.37/1.33  tff(c_468, plain, (![A_70, B_71]: (~r2_hidden(A_70, B_71) | k3_xboole_0(k1_tarski(A_70), B_71)=k1_tarski(A_70))), inference(resolution, [status(thm)], [c_434, c_6])).
% 2.37/1.33  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.37/1.33  tff(c_509, plain, (![B_72, A_73]: (k3_xboole_0(B_72, k1_tarski(A_73))=k1_tarski(A_73) | ~r2_hidden(A_73, B_72))), inference(superposition, [status(thm), theory('equality')], [c_468, c_2])).
% 2.37/1.33  tff(c_36, plain, (k3_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.37/1.33  tff(c_39, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_3'))!=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_36])).
% 2.37/1.33  tff(c_535, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_509, c_39])).
% 2.37/1.33  tff(c_565, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_535])).
% 2.37/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.33  
% 2.37/1.33  Inference rules
% 2.37/1.33  ----------------------
% 2.37/1.33  #Ref     : 0
% 2.37/1.33  #Sup     : 137
% 2.37/1.33  #Fact    : 0
% 2.37/1.33  #Define  : 0
% 2.37/1.33  #Split   : 0
% 2.37/1.33  #Chain   : 0
% 2.37/1.33  #Close   : 0
% 2.37/1.33  
% 2.37/1.33  Ordering : KBO
% 2.37/1.33  
% 2.37/1.33  Simplification rules
% 2.37/1.33  ----------------------
% 2.37/1.33  #Subsume      : 8
% 2.37/1.33  #Demod        : 8
% 2.37/1.33  #Tautology    : 43
% 2.37/1.33  #SimpNegUnit  : 0
% 2.37/1.33  #BackRed      : 0
% 2.37/1.33  
% 2.37/1.33  #Partial instantiations: 0
% 2.37/1.33  #Strategies tried      : 1
% 2.37/1.33  
% 2.37/1.33  Timing (in seconds)
% 2.37/1.33  ----------------------
% 2.37/1.33  Preprocessing        : 0.31
% 2.37/1.33  Parsing              : 0.15
% 2.37/1.33  CNF conversion       : 0.02
% 2.37/1.33  Main loop            : 0.27
% 2.37/1.33  Inferencing          : 0.10
% 2.37/1.33  Reduction            : 0.09
% 2.37/1.33  Demodulation         : 0.07
% 2.37/1.33  BG Simplification    : 0.02
% 2.37/1.33  Subsumption          : 0.05
% 2.37/1.33  Abstraction          : 0.02
% 2.37/1.33  MUC search           : 0.00
% 2.37/1.33  Cooper               : 0.00
% 2.37/1.33  Total                : 0.60
% 2.37/1.33  Index Insertion      : 0.00
% 2.37/1.33  Index Deletion       : 0.00
% 2.37/1.33  Index Matching       : 0.00
% 2.37/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
