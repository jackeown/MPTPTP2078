%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:15 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   44 (  55 expanded)
%              Number of leaves         :   25 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   47 (  68 expanded)
%              Number of equality atoms :   15 (  22 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_5 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(k1_tarski(A),B)
        | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_50,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_170,plain,(
    ! [B_60,A_61] :
      ( k3_xboole_0(B_60,k1_tarski(A_61)) = k1_tarski(A_61)
      | ~ r2_hidden(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_48,plain,(
    k3_xboole_0(k1_tarski('#skF_6'),'#skF_7') != k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_51,plain,(
    k3_xboole_0('#skF_7',k1_tarski('#skF_6')) != k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_48])).

tff(c_207,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_51])).

tff(c_209,plain,(
    ! [A_62,B_63] :
      ( r2_hidden('#skF_3'(A_62,B_63),k3_xboole_0(A_62,B_63))
      | r1_xboole_0(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_26,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_136,plain,(
    ! [D_45,A_46,B_47] :
      ( r2_hidden(D_45,A_46)
      | ~ r2_hidden(D_45,k4_xboole_0(A_46,B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_139,plain,(
    ! [D_45,A_14,B_15] :
      ( r2_hidden(D_45,A_14)
      | ~ r2_hidden(D_45,k3_xboole_0(A_14,B_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_136])).

tff(c_236,plain,(
    ! [A_66,B_67] :
      ( r2_hidden('#skF_3'(A_66,B_67),A_66)
      | r1_xboole_0(A_66,B_67) ) ),
    inference(resolution,[status(thm)],[c_209,c_139])).

tff(c_28,plain,(
    ! [C_20,A_16] :
      ( C_20 = A_16
      | ~ r2_hidden(C_20,k1_tarski(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_473,plain,(
    ! [A_93,B_94] :
      ( '#skF_3'(k1_tarski(A_93),B_94) = A_93
      | r1_xboole_0(k1_tarski(A_93),B_94) ) ),
    inference(resolution,[status(thm)],[c_236,c_28])).

tff(c_480,plain,(
    '#skF_3'(k1_tarski('#skF_6'),'#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_473,c_50])).

tff(c_147,plain,(
    ! [D_51,A_52,B_53] :
      ( r2_hidden(D_51,A_52)
      | ~ r2_hidden(D_51,k3_xboole_0(A_52,B_53)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_136])).

tff(c_150,plain,(
    ! [D_51,A_1,B_2] :
      ( r2_hidden(D_51,A_1)
      | ~ r2_hidden(D_51,k3_xboole_0(B_2,A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_147])).

tff(c_231,plain,(
    ! [A_62,B_63] :
      ( r2_hidden('#skF_3'(A_62,B_63),B_63)
      | r1_xboole_0(A_62,B_63) ) ),
    inference(resolution,[status(thm)],[c_209,c_150])).

tff(c_484,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | r1_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_231])).

tff(c_494,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_207,c_484])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:38:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.31  
% 2.41/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.31  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_5 > #skF_4
% 2.41/1.31  
% 2.41/1.31  %Foreground sorts:
% 2.41/1.31  
% 2.41/1.31  
% 2.41/1.31  %Background operators:
% 2.41/1.31  
% 2.41/1.31  
% 2.41/1.31  %Foreground operators:
% 2.41/1.31  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.41/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.41/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.41/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.41/1.31  tff('#skF_7', type, '#skF_7': $i).
% 2.41/1.31  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.41/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.41/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.41/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.41/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.41/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.41/1.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.41/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.41/1.31  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.41/1.31  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.41/1.31  
% 2.41/1.32  tff(f_75, negated_conjecture, ~(![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 2.41/1.32  tff(f_70, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 2.41/1.32  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.41/1.32  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.41/1.32  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.41/1.32  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.41/1.32  tff(f_60, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.41/1.32  tff(c_50, plain, (~r1_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.41/1.32  tff(c_170, plain, (![B_60, A_61]: (k3_xboole_0(B_60, k1_tarski(A_61))=k1_tarski(A_61) | ~r2_hidden(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.41/1.32  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.41/1.32  tff(c_48, plain, (k3_xboole_0(k1_tarski('#skF_6'), '#skF_7')!=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.41/1.32  tff(c_51, plain, (k3_xboole_0('#skF_7', k1_tarski('#skF_6'))!=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_48])).
% 2.41/1.32  tff(c_207, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_170, c_51])).
% 2.41/1.33  tff(c_209, plain, (![A_62, B_63]: (r2_hidden('#skF_3'(A_62, B_63), k3_xboole_0(A_62, B_63)) | r1_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.41/1.33  tff(c_26, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.41/1.33  tff(c_136, plain, (![D_45, A_46, B_47]: (r2_hidden(D_45, A_46) | ~r2_hidden(D_45, k4_xboole_0(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.41/1.33  tff(c_139, plain, (![D_45, A_14, B_15]: (r2_hidden(D_45, A_14) | ~r2_hidden(D_45, k3_xboole_0(A_14, B_15)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_136])).
% 2.41/1.33  tff(c_236, plain, (![A_66, B_67]: (r2_hidden('#skF_3'(A_66, B_67), A_66) | r1_xboole_0(A_66, B_67))), inference(resolution, [status(thm)], [c_209, c_139])).
% 2.41/1.33  tff(c_28, plain, (![C_20, A_16]: (C_20=A_16 | ~r2_hidden(C_20, k1_tarski(A_16)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.41/1.33  tff(c_473, plain, (![A_93, B_94]: ('#skF_3'(k1_tarski(A_93), B_94)=A_93 | r1_xboole_0(k1_tarski(A_93), B_94))), inference(resolution, [status(thm)], [c_236, c_28])).
% 2.41/1.33  tff(c_480, plain, ('#skF_3'(k1_tarski('#skF_6'), '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_473, c_50])).
% 2.41/1.33  tff(c_147, plain, (![D_51, A_52, B_53]: (r2_hidden(D_51, A_52) | ~r2_hidden(D_51, k3_xboole_0(A_52, B_53)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_136])).
% 2.41/1.33  tff(c_150, plain, (![D_51, A_1, B_2]: (r2_hidden(D_51, A_1) | ~r2_hidden(D_51, k3_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_147])).
% 2.41/1.33  tff(c_231, plain, (![A_62, B_63]: (r2_hidden('#skF_3'(A_62, B_63), B_63) | r1_xboole_0(A_62, B_63))), inference(resolution, [status(thm)], [c_209, c_150])).
% 2.41/1.33  tff(c_484, plain, (r2_hidden('#skF_6', '#skF_7') | r1_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_480, c_231])).
% 2.41/1.33  tff(c_494, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_207, c_484])).
% 2.41/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.33  
% 2.41/1.33  Inference rules
% 2.41/1.33  ----------------------
% 2.41/1.33  #Ref     : 0
% 2.41/1.33  #Sup     : 112
% 2.41/1.33  #Fact    : 0
% 2.41/1.33  #Define  : 0
% 2.41/1.33  #Split   : 0
% 2.41/1.33  #Chain   : 0
% 2.41/1.33  #Close   : 0
% 2.41/1.33  
% 2.41/1.33  Ordering : KBO
% 2.41/1.33  
% 2.41/1.33  Simplification rules
% 2.41/1.33  ----------------------
% 2.41/1.33  #Subsume      : 26
% 2.41/1.33  #Demod        : 1
% 2.41/1.33  #Tautology    : 27
% 2.41/1.33  #SimpNegUnit  : 1
% 2.41/1.33  #BackRed      : 0
% 2.41/1.33  
% 2.41/1.33  #Partial instantiations: 0
% 2.41/1.33  #Strategies tried      : 1
% 2.41/1.33  
% 2.41/1.33  Timing (in seconds)
% 2.41/1.33  ----------------------
% 2.41/1.33  Preprocessing        : 0.32
% 2.41/1.33  Parsing              : 0.17
% 2.41/1.33  CNF conversion       : 0.02
% 2.41/1.33  Main loop            : 0.25
% 2.41/1.33  Inferencing          : 0.09
% 2.41/1.33  Reduction            : 0.08
% 2.41/1.33  Demodulation         : 0.06
% 2.41/1.33  BG Simplification    : 0.02
% 2.41/1.33  Subsumption          : 0.05
% 2.41/1.33  Abstraction          : 0.02
% 2.41/1.33  MUC search           : 0.00
% 2.41/1.33  Cooper               : 0.00
% 2.41/1.33  Total                : 0.60
% 2.41/1.33  Index Insertion      : 0.00
% 2.41/1.33  Index Deletion       : 0.00
% 2.41/1.33  Index Matching       : 0.00
% 2.41/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
