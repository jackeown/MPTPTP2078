%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:03 EST 2020

% Result     : Theorem 1.48s
% Output     : CNFRefutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   21 (  28 expanded)
%              Number of leaves         :   11 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :   27 (  49 expanded)
%              Number of equality atoms :   22 (  39 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_tarski(B)
          & A != k1_xboole_0
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

tff(c_10,plain,(
    k1_tarski('#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_13,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_1'(A_9,B_10),A_9)
      | k1_xboole_0 = A_9
      | k1_tarski(B_10) = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [C_5] :
      ( C_5 = '#skF_3'
      | ~ r2_hidden(C_5,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_17,plain,(
    ! [B_10] :
      ( '#skF_1'('#skF_2',B_10) = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | k1_tarski(B_10) = '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_13,c_6])).

tff(c_21,plain,(
    ! [B_11] :
      ( '#skF_1'('#skF_2',B_11) = '#skF_3'
      | k1_tarski(B_11) = '#skF_2' ) ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_17])).

tff(c_32,plain,(
    '#skF_1'('#skF_2','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_21,c_10])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( '#skF_1'(A_1,B_2) != B_2
      | k1_xboole_0 = A_1
      | k1_tarski(B_2) = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_39,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_3') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2])).

tff(c_46,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_8,c_39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:01:52 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.48/1.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.07  
% 1.59/1.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.08  %$ r2_hidden > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.59/1.08  
% 1.59/1.08  %Foreground sorts:
% 1.59/1.08  
% 1.59/1.08  
% 1.59/1.08  %Background operators:
% 1.59/1.08  
% 1.59/1.08  
% 1.59/1.08  %Foreground operators:
% 1.59/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.59/1.08  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.59/1.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.59/1.08  tff('#skF_2', type, '#skF_2': $i).
% 1.59/1.08  tff('#skF_3', type, '#skF_3': $i).
% 1.59/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.08  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.59/1.08  
% 1.59/1.08  tff(f_54, negated_conjecture, ~(![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 1.59/1.08  tff(f_39, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 1.59/1.08  tff(c_10, plain, (k1_tarski('#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.59/1.08  tff(c_8, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.59/1.08  tff(c_13, plain, (![A_9, B_10]: (r2_hidden('#skF_1'(A_9, B_10), A_9) | k1_xboole_0=A_9 | k1_tarski(B_10)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.59/1.08  tff(c_6, plain, (![C_5]: (C_5='#skF_3' | ~r2_hidden(C_5, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.59/1.08  tff(c_17, plain, (![B_10]: ('#skF_1'('#skF_2', B_10)='#skF_3' | k1_xboole_0='#skF_2' | k1_tarski(B_10)='#skF_2')), inference(resolution, [status(thm)], [c_13, c_6])).
% 1.59/1.08  tff(c_21, plain, (![B_11]: ('#skF_1'('#skF_2', B_11)='#skF_3' | k1_tarski(B_11)='#skF_2')), inference(negUnitSimplification, [status(thm)], [c_8, c_17])).
% 1.59/1.08  tff(c_32, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_21, c_10])).
% 1.59/1.08  tff(c_2, plain, (![A_1, B_2]: ('#skF_1'(A_1, B_2)!=B_2 | k1_xboole_0=A_1 | k1_tarski(B_2)=A_1)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.59/1.08  tff(c_39, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_3')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_32, c_2])).
% 1.59/1.08  tff(c_46, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_8, c_39])).
% 1.59/1.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.08  
% 1.59/1.08  Inference rules
% 1.59/1.08  ----------------------
% 1.59/1.08  #Ref     : 0
% 1.59/1.08  #Sup     : 8
% 1.59/1.08  #Fact    : 0
% 1.59/1.08  #Define  : 0
% 1.59/1.08  #Split   : 0
% 1.59/1.08  #Chain   : 0
% 1.59/1.08  #Close   : 0
% 1.59/1.08  
% 1.59/1.08  Ordering : KBO
% 1.59/1.08  
% 1.59/1.08  Simplification rules
% 1.59/1.08  ----------------------
% 1.59/1.08  #Subsume      : 0
% 1.59/1.08  #Demod        : 0
% 1.59/1.08  #Tautology    : 3
% 1.59/1.08  #SimpNegUnit  : 3
% 1.59/1.08  #BackRed      : 0
% 1.59/1.08  
% 1.59/1.08  #Partial instantiations: 0
% 1.59/1.08  #Strategies tried      : 1
% 1.59/1.08  
% 1.59/1.08  Timing (in seconds)
% 1.59/1.08  ----------------------
% 1.59/1.09  Preprocessing        : 0.26
% 1.59/1.09  Parsing              : 0.13
% 1.59/1.09  CNF conversion       : 0.02
% 1.59/1.09  Main loop            : 0.07
% 1.59/1.09  Inferencing          : 0.03
% 1.59/1.09  Reduction            : 0.01
% 1.59/1.09  Demodulation         : 0.00
% 1.59/1.09  BG Simplification    : 0.01
% 1.59/1.09  Subsumption          : 0.01
% 1.59/1.09  Abstraction          : 0.00
% 1.59/1.09  MUC search           : 0.00
% 1.59/1.09  Cooper               : 0.00
% 1.59/1.09  Total                : 0.34
% 1.59/1.09  Index Insertion      : 0.00
% 1.59/1.09  Index Deletion       : 0.00
% 1.59/1.09  Index Matching       : 0.00
% 1.59/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
