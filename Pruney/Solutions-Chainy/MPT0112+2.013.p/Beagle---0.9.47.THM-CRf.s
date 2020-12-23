%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:10 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   33 (  35 expanded)
%              Number of leaves         :   20 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   34 (  39 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r2_xboole_0(A,B)
          & k4_xboole_0(B,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_34,plain,(
    r2_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),B_8)
      | ~ r2_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_32,plain,(
    k4_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | k4_xboole_0(A_14,B_15) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_40,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_79,plain,(
    ! [A_35,B_36] :
      ( k3_xboole_0(A_35,B_36) = A_35
      | k4_xboole_0(A_35,B_36) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_40])).

tff(c_83,plain,(
    k3_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_79])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_102,plain,(
    ! [D_37] :
      ( r2_hidden(D_37,'#skF_4')
      | ~ r2_hidden(D_37,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_4])).

tff(c_125,plain,(
    ! [A_41] :
      ( r2_hidden('#skF_3'(A_41,'#skF_5'),'#skF_4')
      | ~ r2_xboole_0(A_41,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_102])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( ~ r2_hidden('#skF_3'(A_7,B_8),A_7)
      | ~ r2_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_129,plain,(
    ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_125,c_20])).

tff(c_133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_129])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:46:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.16  
% 1.68/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.16  %$ r2_xboole_0 > r2_hidden > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 1.68/1.16  
% 1.68/1.16  %Foreground sorts:
% 1.68/1.16  
% 1.68/1.16  
% 1.68/1.16  %Background operators:
% 1.68/1.16  
% 1.68/1.16  
% 1.68/1.16  %Foreground operators:
% 1.68/1.16  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.68/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.68/1.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.68/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.68/1.16  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.68/1.16  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.68/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.68/1.16  tff('#skF_5', type, '#skF_5': $i).
% 1.68/1.16  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.68/1.16  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.68/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.68/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.68/1.16  
% 1.85/1.17  tff(f_60, negated_conjecture, ~(![A, B]: ~(r2_xboole_0(A, B) & (k4_xboole_0(B, A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_xboole_1)).
% 1.85/1.17  tff(f_44, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_0)).
% 1.85/1.17  tff(f_54, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 1.85/1.17  tff(f_50, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.85/1.17  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.85/1.17  tff(c_34, plain, (r2_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.85/1.17  tff(c_22, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), B_8) | ~r2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.85/1.17  tff(c_32, plain, (k4_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.85/1.17  tff(c_28, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | k4_xboole_0(A_14, B_15)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.85/1.17  tff(c_40, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=A_18 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.85/1.17  tff(c_79, plain, (![A_35, B_36]: (k3_xboole_0(A_35, B_36)=A_35 | k4_xboole_0(A_35, B_36)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_40])).
% 1.85/1.17  tff(c_83, plain, (k3_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_32, c_79])).
% 1.85/1.17  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.85/1.17  tff(c_102, plain, (![D_37]: (r2_hidden(D_37, '#skF_4') | ~r2_hidden(D_37, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_83, c_4])).
% 1.85/1.17  tff(c_125, plain, (![A_41]: (r2_hidden('#skF_3'(A_41, '#skF_5'), '#skF_4') | ~r2_xboole_0(A_41, '#skF_5'))), inference(resolution, [status(thm)], [c_22, c_102])).
% 1.85/1.17  tff(c_20, plain, (![A_7, B_8]: (~r2_hidden('#skF_3'(A_7, B_8), A_7) | ~r2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.85/1.17  tff(c_129, plain, (~r2_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_125, c_20])).
% 1.85/1.17  tff(c_133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_129])).
% 1.85/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.17  
% 1.85/1.17  Inference rules
% 1.85/1.17  ----------------------
% 1.85/1.17  #Ref     : 0
% 1.85/1.17  #Sup     : 23
% 1.85/1.17  #Fact    : 0
% 1.85/1.17  #Define  : 0
% 1.85/1.17  #Split   : 0
% 1.85/1.17  #Chain   : 0
% 1.85/1.17  #Close   : 0
% 1.85/1.17  
% 1.85/1.17  Ordering : KBO
% 1.85/1.17  
% 1.85/1.17  Simplification rules
% 1.85/1.17  ----------------------
% 1.85/1.17  #Subsume      : 0
% 1.85/1.17  #Demod        : 2
% 1.85/1.17  #Tautology    : 13
% 1.85/1.17  #SimpNegUnit  : 0
% 1.85/1.17  #BackRed      : 0
% 1.85/1.17  
% 1.85/1.17  #Partial instantiations: 0
% 1.85/1.17  #Strategies tried      : 1
% 1.85/1.17  
% 1.85/1.17  Timing (in seconds)
% 1.85/1.17  ----------------------
% 1.85/1.17  Preprocessing        : 0.28
% 1.85/1.17  Parsing              : 0.15
% 1.85/1.17  CNF conversion       : 0.02
% 1.85/1.17  Main loop            : 0.13
% 1.85/1.17  Inferencing          : 0.05
% 1.85/1.17  Reduction            : 0.03
% 1.85/1.17  Demodulation         : 0.03
% 1.85/1.17  BG Simplification    : 0.01
% 1.85/1.17  Subsumption          : 0.03
% 1.85/1.17  Abstraction          : 0.01
% 1.85/1.17  MUC search           : 0.00
% 1.85/1.17  Cooper               : 0.00
% 1.85/1.17  Total                : 0.44
% 1.85/1.17  Index Insertion      : 0.00
% 1.85/1.17  Index Deletion       : 0.00
% 1.85/1.17  Index Matching       : 0.00
% 1.85/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
