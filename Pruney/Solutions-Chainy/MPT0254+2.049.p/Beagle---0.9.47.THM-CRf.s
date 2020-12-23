%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:26 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   43 (  45 expanded)
%              Number of leaves         :   26 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   37 (  41 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_3

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_56,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_43,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_48,plain,(
    ! [A_21] : k2_tarski(A_21,A_21) = k1_tarski(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_32,plain,(
    ! [D_20,A_15] : r2_hidden(D_20,k2_tarski(A_15,D_20)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_59,plain,(
    ! [B_28,A_29] :
      ( ~ r2_hidden(B_28,A_29)
      | ~ v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_83,plain,(
    ! [A_31,D_32] : ~ v1_xboole_0(k2_tarski(A_31,D_32)) ),
    inference(resolution,[status(thm)],[c_32,c_59])).

tff(c_85,plain,(
    ! [A_21] : ~ v1_xboole_0(k1_tarski(A_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_83])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_92,plain,(
    ! [B_35,A_36] : k2_xboole_0(B_35,A_36) = k2_xboole_0(A_36,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_52,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_107,plain,(
    k2_xboole_0('#skF_7',k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_52])).

tff(c_159,plain,(
    ! [D_40,B_41,A_42] :
      ( ~ r2_hidden(D_40,B_41)
      | r2_hidden(D_40,k2_xboole_0(A_42,B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_189,plain,(
    ! [A_45,B_46,D_47] :
      ( ~ v1_xboole_0(k2_xboole_0(A_45,B_46))
      | ~ r2_hidden(D_47,B_46) ) ),
    inference(resolution,[status(thm)],[c_159,c_4])).

tff(c_191,plain,(
    ! [D_47] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(D_47,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_189])).

tff(c_202,plain,(
    ! [D_48] : ~ r2_hidden(D_48,k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_191])).

tff(c_206,plain,(
    v1_xboole_0(k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_6,c_202])).

tff(c_213,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_206])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:53:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.23  
% 1.96/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.24  %$ r2_hidden > v1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_3
% 2.07/1.24  
% 2.07/1.24  %Foreground sorts:
% 2.07/1.24  
% 2.07/1.24  
% 2.07/1.24  %Background operators:
% 2.07/1.24  
% 2.07/1.24  
% 2.07/1.24  %Foreground operators:
% 2.07/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.07/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.07/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.07/1.24  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.07/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.07/1.24  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.07/1.24  tff('#skF_7', type, '#skF_7': $i).
% 2.07/1.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.07/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.07/1.24  tff('#skF_6', type, '#skF_6': $i).
% 2.07/1.24  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.07/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.07/1.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.07/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.24  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.07/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.07/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.07/1.24  
% 2.07/1.25  tff(f_56, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.07/1.25  tff(f_54, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.07/1.25  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.07/1.25  tff(f_43, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.07/1.25  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.07/1.25  tff(f_62, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.07/1.25  tff(f_42, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.07/1.25  tff(c_48, plain, (![A_21]: (k2_tarski(A_21, A_21)=k1_tarski(A_21))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.07/1.25  tff(c_32, plain, (![D_20, A_15]: (r2_hidden(D_20, k2_tarski(A_15, D_20)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.07/1.25  tff(c_59, plain, (![B_28, A_29]: (~r2_hidden(B_28, A_29) | ~v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.07/1.25  tff(c_83, plain, (![A_31, D_32]: (~v1_xboole_0(k2_tarski(A_31, D_32)))), inference(resolution, [status(thm)], [c_32, c_59])).
% 2.07/1.25  tff(c_85, plain, (![A_21]: (~v1_xboole_0(k1_tarski(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_83])).
% 2.07/1.25  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.07/1.25  tff(c_26, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.07/1.25  tff(c_92, plain, (![B_35, A_36]: (k2_xboole_0(B_35, A_36)=k2_xboole_0(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.07/1.25  tff(c_52, plain, (k2_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.07/1.25  tff(c_107, plain, (k2_xboole_0('#skF_7', k1_tarski('#skF_6'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_92, c_52])).
% 2.07/1.25  tff(c_159, plain, (![D_40, B_41, A_42]: (~r2_hidden(D_40, B_41) | r2_hidden(D_40, k2_xboole_0(A_42, B_41)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.07/1.25  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.07/1.25  tff(c_189, plain, (![A_45, B_46, D_47]: (~v1_xboole_0(k2_xboole_0(A_45, B_46)) | ~r2_hidden(D_47, B_46))), inference(resolution, [status(thm)], [c_159, c_4])).
% 2.07/1.25  tff(c_191, plain, (![D_47]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(D_47, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_107, c_189])).
% 2.07/1.25  tff(c_202, plain, (![D_48]: (~r2_hidden(D_48, k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_191])).
% 2.07/1.25  tff(c_206, plain, (v1_xboole_0(k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_6, c_202])).
% 2.07/1.25  tff(c_213, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_206])).
% 2.07/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.25  
% 2.07/1.25  Inference rules
% 2.07/1.25  ----------------------
% 2.07/1.25  #Ref     : 0
% 2.07/1.25  #Sup     : 40
% 2.07/1.25  #Fact    : 0
% 2.07/1.25  #Define  : 0
% 2.07/1.25  #Split   : 0
% 2.07/1.25  #Chain   : 0
% 2.07/1.25  #Close   : 0
% 2.07/1.25  
% 2.07/1.25  Ordering : KBO
% 2.07/1.25  
% 2.07/1.25  Simplification rules
% 2.07/1.25  ----------------------
% 2.07/1.25  #Subsume      : 4
% 2.07/1.25  #Demod        : 7
% 2.07/1.25  #Tautology    : 21
% 2.07/1.25  #SimpNegUnit  : 1
% 2.07/1.25  #BackRed      : 0
% 2.07/1.25  
% 2.07/1.25  #Partial instantiations: 0
% 2.07/1.25  #Strategies tried      : 1
% 2.07/1.25  
% 2.07/1.25  Timing (in seconds)
% 2.07/1.25  ----------------------
% 2.07/1.25  Preprocessing        : 0.31
% 2.07/1.25  Parsing              : 0.16
% 2.07/1.25  CNF conversion       : 0.02
% 2.07/1.25  Main loop            : 0.15
% 2.07/1.25  Inferencing          : 0.04
% 2.07/1.25  Reduction            : 0.06
% 2.07/1.25  Demodulation         : 0.04
% 2.07/1.25  BG Simplification    : 0.01
% 2.07/1.25  Subsumption          : 0.03
% 2.07/1.25  Abstraction          : 0.01
% 2.07/1.25  MUC search           : 0.00
% 2.07/1.25  Cooper               : 0.00
% 2.07/1.25  Total                : 0.48
% 2.07/1.25  Index Insertion      : 0.00
% 2.07/1.25  Index Deletion       : 0.00
% 2.07/1.25  Index Matching       : 0.00
% 2.07/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
