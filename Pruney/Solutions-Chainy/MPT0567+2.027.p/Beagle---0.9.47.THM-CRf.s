%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:18 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   43 (  46 expanded)
%              Number of leaves         :   25 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :   46 (  50 expanded)
%              Number of equality atoms :   12 (  15 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_56,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_48,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_54,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_52,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_28,plain,(
    k10_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_30,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_236,plain,(
    ! [A_55,B_56,C_57] :
      ( r2_hidden('#skF_3'(A_55,B_56,C_57),B_56)
      | ~ r2_hidden(A_55,k10_relat_1(C_57,B_56))
      | ~ v1_relat_1(C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18,plain,(
    ! [A_15] : r1_xboole_0(A_15,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_42,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k4_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_60,plain,(
    ! [A_27] : k4_xboole_0(A_27,A_27) = k3_xboole_0(A_27,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_42])).

tff(c_70,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_12])).

tff(c_85,plain,(
    ! [A_28,B_29,C_30] :
      ( ~ r1_xboole_0(A_28,B_29)
      | ~ r2_hidden(C_30,k3_xboole_0(A_28,B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_88,plain,(
    ! [C_30] :
      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
      | ~ r2_hidden(C_30,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_85])).

tff(c_90,plain,(
    ! [C_30] : ~ r2_hidden(C_30,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_88])).

tff(c_250,plain,(
    ! [A_58,C_59] :
      ( ~ r2_hidden(A_58,k10_relat_1(C_59,k1_xboole_0))
      | ~ v1_relat_1(C_59) ) ),
    inference(resolution,[status(thm)],[c_236,c_90])).

tff(c_261,plain,(
    ! [C_60,B_61] :
      ( ~ v1_relat_1(C_60)
      | r1_tarski(k10_relat_1(C_60,k1_xboole_0),B_61) ) ),
    inference(resolution,[status(thm)],[c_6,c_250])).

tff(c_14,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_267,plain,(
    ! [C_62] :
      ( k10_relat_1(C_62,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(C_62) ) ),
    inference(resolution,[status(thm)],[c_261,c_14])).

tff(c_270,plain,(
    k10_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_267])).

tff(c_274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_270])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:36:25 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.37  
% 2.02/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.37  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.02/1.37  
% 2.02/1.37  %Foreground sorts:
% 2.02/1.37  
% 2.02/1.37  
% 2.02/1.37  %Background operators:
% 2.02/1.37  
% 2.02/1.37  
% 2.02/1.37  %Foreground operators:
% 2.02/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.02/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.02/1.37  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.02/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.02/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.02/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.02/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.37  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.02/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.02/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.02/1.37  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.02/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.02/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.02/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.02/1.37  
% 2.02/1.38  tff(f_72, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_relat_1)).
% 2.02/1.38  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.02/1.38  tff(f_67, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 2.02/1.38  tff(f_56, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.02/1.38  tff(f_48, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.02/1.38  tff(f_54, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.02/1.38  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.02/1.38  tff(f_52, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.02/1.38  tff(c_28, plain, (k10_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.02/1.38  tff(c_30, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.02/1.38  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.02/1.38  tff(c_236, plain, (![A_55, B_56, C_57]: (r2_hidden('#skF_3'(A_55, B_56, C_57), B_56) | ~r2_hidden(A_55, k10_relat_1(C_57, B_56)) | ~v1_relat_1(C_57))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.02/1.38  tff(c_18, plain, (![A_15]: (r1_xboole_0(A_15, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.02/1.38  tff(c_12, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.02/1.38  tff(c_42, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k4_xboole_0(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.02/1.38  tff(c_60, plain, (![A_27]: (k4_xboole_0(A_27, A_27)=k3_xboole_0(A_27, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_42])).
% 2.02/1.38  tff(c_70, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_60, c_12])).
% 2.02/1.38  tff(c_85, plain, (![A_28, B_29, C_30]: (~r1_xboole_0(A_28, B_29) | ~r2_hidden(C_30, k3_xboole_0(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.02/1.38  tff(c_88, plain, (![C_30]: (~r1_xboole_0(k1_xboole_0, k1_xboole_0) | ~r2_hidden(C_30, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_70, c_85])).
% 2.02/1.38  tff(c_90, plain, (![C_30]: (~r2_hidden(C_30, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_88])).
% 2.02/1.38  tff(c_250, plain, (![A_58, C_59]: (~r2_hidden(A_58, k10_relat_1(C_59, k1_xboole_0)) | ~v1_relat_1(C_59))), inference(resolution, [status(thm)], [c_236, c_90])).
% 2.02/1.38  tff(c_261, plain, (![C_60, B_61]: (~v1_relat_1(C_60) | r1_tarski(k10_relat_1(C_60, k1_xboole_0), B_61))), inference(resolution, [status(thm)], [c_6, c_250])).
% 2.02/1.38  tff(c_14, plain, (![A_12]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.02/1.38  tff(c_267, plain, (![C_62]: (k10_relat_1(C_62, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(C_62))), inference(resolution, [status(thm)], [c_261, c_14])).
% 2.02/1.38  tff(c_270, plain, (k10_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_267])).
% 2.02/1.38  tff(c_274, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_270])).
% 2.02/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.38  
% 2.02/1.38  Inference rules
% 2.02/1.38  ----------------------
% 2.02/1.38  #Ref     : 0
% 2.02/1.38  #Sup     : 52
% 2.02/1.38  #Fact    : 0
% 2.02/1.38  #Define  : 0
% 2.02/1.38  #Split   : 0
% 2.02/1.38  #Chain   : 0
% 2.02/1.38  #Close   : 0
% 2.02/1.38  
% 2.02/1.38  Ordering : KBO
% 2.02/1.38  
% 2.02/1.38  Simplification rules
% 2.02/1.38  ----------------------
% 2.02/1.38  #Subsume      : 2
% 2.02/1.38  #Demod        : 15
% 2.02/1.38  #Tautology    : 28
% 2.02/1.38  #SimpNegUnit  : 2
% 2.02/1.38  #BackRed      : 1
% 2.02/1.38  
% 2.02/1.38  #Partial instantiations: 0
% 2.02/1.38  #Strategies tried      : 1
% 2.02/1.38  
% 2.02/1.38  Timing (in seconds)
% 2.02/1.38  ----------------------
% 2.02/1.38  Preprocessing        : 0.38
% 2.02/1.38  Parsing              : 0.24
% 2.02/1.38  CNF conversion       : 0.02
% 2.02/1.38  Main loop            : 0.17
% 2.02/1.38  Inferencing          : 0.07
% 2.02/1.38  Reduction            : 0.05
% 2.02/1.38  Demodulation         : 0.03
% 2.02/1.38  BG Simplification    : 0.01
% 2.02/1.38  Subsumption          : 0.03
% 2.02/1.38  Abstraction          : 0.01
% 2.02/1.38  MUC search           : 0.00
% 2.02/1.38  Cooper               : 0.00
% 2.02/1.38  Total                : 0.58
% 2.02/1.38  Index Insertion      : 0.00
% 2.02/1.38  Index Deletion       : 0.00
% 2.02/1.38  Index Matching       : 0.00
% 2.02/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
