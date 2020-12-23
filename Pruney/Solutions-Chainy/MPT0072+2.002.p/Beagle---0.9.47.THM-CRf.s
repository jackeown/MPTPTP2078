%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:24 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   42 (  80 expanded)
%              Number of leaves         :   19 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   43 ( 102 expanded)
%              Number of equality atoms :   10 (  36 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_60,negated_conjecture,(
    ~ ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_95,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k4_xboole_0(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_30,plain,(
    ! [A_18] : k4_xboole_0(k1_xboole_0,A_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_125,plain,(
    ! [B_29] : k3_xboole_0(k1_xboole_0,B_29) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_30])).

tff(c_24,plain,(
    ! [A_9,B_10,C_13] :
      ( ~ r1_xboole_0(A_9,B_10)
      | ~ r2_hidden(C_13,k3_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_130,plain,(
    ! [B_29,C_13] :
      ( ~ r1_xboole_0(k1_xboole_0,B_29)
      | ~ r2_hidden(C_13,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_24])).

tff(c_212,plain,(
    ! [C_13] : ~ r2_hidden(C_13,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_130])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_133,plain,(
    ! [B_29] : k3_xboole_0(B_29,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_2])).

tff(c_214,plain,(
    ! [A_42,B_43] :
      ( r2_hidden('#skF_3'(A_42,B_43),k3_xboole_0(A_42,B_43))
      | r1_xboole_0(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_220,plain,(
    ! [B_29] :
      ( r2_hidden('#skF_3'(B_29,k1_xboole_0),k1_xboole_0)
      | r1_xboole_0(B_29,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_214])).

tff(c_231,plain,(
    ! [B_29] : r1_xboole_0(B_29,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_220])).

tff(c_32,plain,(
    ~ r1_xboole_0('#skF_4',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_236,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_32])).

tff(c_237,plain,(
    ! [B_29] : ~ r1_xboole_0(k1_xboole_0,B_29) ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_105,plain,(
    ! [B_28] : k3_xboole_0(k1_xboole_0,B_28) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_30])).

tff(c_289,plain,(
    ! [A_56,B_57] :
      ( r2_hidden('#skF_3'(A_56,B_57),k3_xboole_0(A_56,B_57))
      | r1_xboole_0(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_306,plain,(
    ! [B_28] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_28),k1_xboole_0)
      | r1_xboole_0(k1_xboole_0,B_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_289])).

tff(c_318,plain,(
    ! [B_28] : r2_hidden('#skF_3'(k1_xboole_0,B_28),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_237,c_306])).

tff(c_319,plain,(
    ! [B_58] : r2_hidden('#skF_3'(k1_xboole_0,B_58),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_237,c_306])).

tff(c_151,plain,(
    ! [D_30,B_31,A_32] :
      ( ~ r2_hidden(D_30,B_31)
      | ~ r2_hidden(D_30,k4_xboole_0(A_32,B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_160,plain,(
    ! [D_30,A_18] :
      ( ~ r2_hidden(D_30,A_18)
      | ~ r2_hidden(D_30,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_151])).

tff(c_323,plain,(
    ! [B_58] : ~ r2_hidden('#skF_3'(k1_xboole_0,B_58),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_319,c_160])).

tff(c_328,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_323])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:16:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.20  
% 1.91/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.20  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 1.91/1.20  
% 1.91/1.20  %Foreground sorts:
% 1.91/1.20  
% 1.91/1.20  
% 1.91/1.20  %Background operators:
% 1.91/1.20  
% 1.91/1.20  
% 1.91/1.20  %Foreground operators:
% 1.91/1.20  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.91/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.91/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.91/1.20  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.91/1.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.91/1.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.91/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.91/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.91/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.91/1.20  
% 1.91/1.22  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.91/1.22  tff(f_57, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 1.91/1.22  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.91/1.22  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.91/1.22  tff(f_60, negated_conjecture, ~(![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.91/1.22  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.91/1.22  tff(c_95, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k4_xboole_0(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.91/1.22  tff(c_30, plain, (![A_18]: (k4_xboole_0(k1_xboole_0, A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.91/1.22  tff(c_125, plain, (![B_29]: (k3_xboole_0(k1_xboole_0, B_29)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_95, c_30])).
% 1.91/1.22  tff(c_24, plain, (![A_9, B_10, C_13]: (~r1_xboole_0(A_9, B_10) | ~r2_hidden(C_13, k3_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.91/1.22  tff(c_130, plain, (![B_29, C_13]: (~r1_xboole_0(k1_xboole_0, B_29) | ~r2_hidden(C_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_125, c_24])).
% 1.91/1.22  tff(c_212, plain, (![C_13]: (~r2_hidden(C_13, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_130])).
% 1.91/1.22  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.91/1.22  tff(c_133, plain, (![B_29]: (k3_xboole_0(B_29, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_125, c_2])).
% 1.91/1.22  tff(c_214, plain, (![A_42, B_43]: (r2_hidden('#skF_3'(A_42, B_43), k3_xboole_0(A_42, B_43)) | r1_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.91/1.22  tff(c_220, plain, (![B_29]: (r2_hidden('#skF_3'(B_29, k1_xboole_0), k1_xboole_0) | r1_xboole_0(B_29, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_133, c_214])).
% 1.91/1.22  tff(c_231, plain, (![B_29]: (r1_xboole_0(B_29, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_212, c_220])).
% 1.91/1.22  tff(c_32, plain, (~r1_xboole_0('#skF_4', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.91/1.22  tff(c_236, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_231, c_32])).
% 1.91/1.22  tff(c_237, plain, (![B_29]: (~r1_xboole_0(k1_xboole_0, B_29))), inference(splitRight, [status(thm)], [c_130])).
% 1.91/1.22  tff(c_105, plain, (![B_28]: (k3_xboole_0(k1_xboole_0, B_28)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_95, c_30])).
% 1.91/1.22  tff(c_289, plain, (![A_56, B_57]: (r2_hidden('#skF_3'(A_56, B_57), k3_xboole_0(A_56, B_57)) | r1_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.91/1.22  tff(c_306, plain, (![B_28]: (r2_hidden('#skF_3'(k1_xboole_0, B_28), k1_xboole_0) | r1_xboole_0(k1_xboole_0, B_28))), inference(superposition, [status(thm), theory('equality')], [c_105, c_289])).
% 1.91/1.22  tff(c_318, plain, (![B_28]: (r2_hidden('#skF_3'(k1_xboole_0, B_28), k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_237, c_306])).
% 1.91/1.22  tff(c_319, plain, (![B_58]: (r2_hidden('#skF_3'(k1_xboole_0, B_58), k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_237, c_306])).
% 1.91/1.22  tff(c_151, plain, (![D_30, B_31, A_32]: (~r2_hidden(D_30, B_31) | ~r2_hidden(D_30, k4_xboole_0(A_32, B_31)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.91/1.22  tff(c_160, plain, (![D_30, A_18]: (~r2_hidden(D_30, A_18) | ~r2_hidden(D_30, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_151])).
% 1.91/1.22  tff(c_323, plain, (![B_58]: (~r2_hidden('#skF_3'(k1_xboole_0, B_58), k1_xboole_0))), inference(resolution, [status(thm)], [c_319, c_160])).
% 1.91/1.22  tff(c_328, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_318, c_323])).
% 1.91/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.22  
% 1.91/1.22  Inference rules
% 1.91/1.22  ----------------------
% 1.91/1.22  #Ref     : 0
% 1.91/1.22  #Sup     : 74
% 1.91/1.22  #Fact    : 0
% 1.91/1.22  #Define  : 0
% 1.91/1.22  #Split   : 2
% 1.91/1.22  #Chain   : 0
% 1.91/1.22  #Close   : 0
% 1.91/1.22  
% 1.91/1.22  Ordering : KBO
% 1.91/1.22  
% 1.91/1.22  Simplification rules
% 1.91/1.22  ----------------------
% 1.91/1.22  #Subsume      : 11
% 1.91/1.22  #Demod        : 12
% 1.91/1.22  #Tautology    : 35
% 1.91/1.22  #SimpNegUnit  : 6
% 1.91/1.22  #BackRed      : 1
% 1.91/1.22  
% 1.91/1.22  #Partial instantiations: 0
% 1.91/1.22  #Strategies tried      : 1
% 1.91/1.22  
% 1.91/1.22  Timing (in seconds)
% 1.91/1.22  ----------------------
% 1.91/1.22  Preprocessing        : 0.27
% 1.91/1.22  Parsing              : 0.14
% 1.91/1.22  CNF conversion       : 0.02
% 1.91/1.22  Main loop            : 0.18
% 1.91/1.22  Inferencing          : 0.07
% 1.91/1.22  Reduction            : 0.06
% 1.91/1.22  Demodulation         : 0.04
% 1.91/1.22  BG Simplification    : 0.01
% 1.91/1.22  Subsumption          : 0.04
% 1.91/1.22  Abstraction          : 0.01
% 1.91/1.22  MUC search           : 0.00
% 1.91/1.22  Cooper               : 0.00
% 1.91/1.22  Total                : 0.48
% 1.91/1.22  Index Insertion      : 0.00
% 1.91/1.22  Index Deletion       : 0.00
% 1.91/1.22  Index Matching       : 0.00
% 1.91/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
