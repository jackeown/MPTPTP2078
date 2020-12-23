%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:43 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   46 (  66 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   48 (  88 expanded)
%              Number of equality atoms :   21 (  40 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_55,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_28,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_22,plain,(
    k10_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_206,plain,(
    ! [B_42,A_43] :
      ( r1_xboole_0(k2_relat_1(B_42),A_43)
      | k10_relat_1(B_42,A_43) != k1_xboole_0
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_14,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_24,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_77,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(A_23,B_24) = k1_xboole_0
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_85,plain,(
    k4_xboole_0('#skF_3',k2_relat_1('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_77])).

tff(c_90,plain,(
    ! [A_25,B_26] : k4_xboole_0(A_25,k4_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_105,plain,(
    k3_xboole_0('#skF_3',k2_relat_1('#skF_4')) = k4_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_90])).

tff(c_111,plain,(
    k3_xboole_0('#skF_3',k2_relat_1('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_105])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_141,plain,(
    ! [A_28,B_29,C_30] :
      ( ~ r1_xboole_0(A_28,B_29)
      | ~ r2_hidden(C_30,k3_xboole_0(A_28,B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_162,plain,(
    ! [B_33,A_34,C_35] :
      ( ~ r1_xboole_0(B_33,A_34)
      | ~ r2_hidden(C_35,k3_xboole_0(A_34,B_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_141])).

tff(c_168,plain,(
    ! [C_35] :
      ( ~ r1_xboole_0(k2_relat_1('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_35,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_162])).

tff(c_181,plain,(
    ~ r1_xboole_0(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_168])).

tff(c_211,plain,
    ( k10_relat_1('#skF_4','#skF_3') != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_206,c_181])).

tff(c_222,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_22,c_211])).

tff(c_225,plain,(
    ! [C_44] : ~ r2_hidden(C_44,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_229,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_8,c_225])).

tff(c_233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_229])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:31:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.20  
% 1.92/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.20  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.02/1.20  
% 2.02/1.20  %Foreground sorts:
% 2.02/1.20  
% 2.02/1.20  
% 2.02/1.20  %Background operators:
% 2.02/1.20  
% 2.02/1.20  
% 2.02/1.20  %Foreground operators:
% 2.02/1.20  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.02/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.02/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.02/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.02/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.02/1.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.02/1.20  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.20  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.02/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.02/1.20  tff('#skF_4', type, '#skF_4': $i).
% 2.02/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.02/1.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.02/1.20  
% 2.02/1.21  tff(f_74, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_relat_1)).
% 2.02/1.21  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.02/1.21  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 2.02/1.21  tff(f_55, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.02/1.21  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.02/1.21  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.02/1.21  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.02/1.21  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.02/1.21  tff(c_26, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.02/1.21  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.02/1.21  tff(c_28, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.02/1.21  tff(c_22, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.02/1.21  tff(c_206, plain, (![B_42, A_43]: (r1_xboole_0(k2_relat_1(B_42), A_43) | k10_relat_1(B_42, A_43)!=k1_xboole_0 | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.02/1.21  tff(c_14, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.02/1.21  tff(c_24, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.02/1.21  tff(c_77, plain, (![A_23, B_24]: (k4_xboole_0(A_23, B_24)=k1_xboole_0 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.02/1.21  tff(c_85, plain, (k4_xboole_0('#skF_3', k2_relat_1('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_77])).
% 2.02/1.21  tff(c_90, plain, (![A_25, B_26]: (k4_xboole_0(A_25, k4_xboole_0(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.02/1.21  tff(c_105, plain, (k3_xboole_0('#skF_3', k2_relat_1('#skF_4'))=k4_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_85, c_90])).
% 2.02/1.21  tff(c_111, plain, (k3_xboole_0('#skF_3', k2_relat_1('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_105])).
% 2.02/1.21  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.02/1.21  tff(c_141, plain, (![A_28, B_29, C_30]: (~r1_xboole_0(A_28, B_29) | ~r2_hidden(C_30, k3_xboole_0(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.02/1.21  tff(c_162, plain, (![B_33, A_34, C_35]: (~r1_xboole_0(B_33, A_34) | ~r2_hidden(C_35, k3_xboole_0(A_34, B_33)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_141])).
% 2.02/1.21  tff(c_168, plain, (![C_35]: (~r1_xboole_0(k2_relat_1('#skF_4'), '#skF_3') | ~r2_hidden(C_35, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_111, c_162])).
% 2.02/1.21  tff(c_181, plain, (~r1_xboole_0(k2_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_168])).
% 2.02/1.21  tff(c_211, plain, (k10_relat_1('#skF_4', '#skF_3')!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_206, c_181])).
% 2.02/1.21  tff(c_222, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_22, c_211])).
% 2.02/1.21  tff(c_225, plain, (![C_44]: (~r2_hidden(C_44, '#skF_3'))), inference(splitRight, [status(thm)], [c_168])).
% 2.02/1.21  tff(c_229, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_8, c_225])).
% 2.02/1.21  tff(c_233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_229])).
% 2.02/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.21  
% 2.02/1.21  Inference rules
% 2.02/1.21  ----------------------
% 2.02/1.21  #Ref     : 0
% 2.02/1.21  #Sup     : 52
% 2.02/1.21  #Fact    : 0
% 2.02/1.21  #Define  : 0
% 2.02/1.21  #Split   : 3
% 2.02/1.21  #Chain   : 0
% 2.02/1.21  #Close   : 0
% 2.02/1.21  
% 2.02/1.21  Ordering : KBO
% 2.02/1.21  
% 2.02/1.21  Simplification rules
% 2.02/1.21  ----------------------
% 2.02/1.21  #Subsume      : 3
% 2.02/1.21  #Demod        : 4
% 2.02/1.21  #Tautology    : 25
% 2.02/1.21  #SimpNegUnit  : 3
% 2.02/1.21  #BackRed      : 0
% 2.02/1.21  
% 2.02/1.21  #Partial instantiations: 0
% 2.02/1.21  #Strategies tried      : 1
% 2.02/1.22  
% 2.02/1.22  Timing (in seconds)
% 2.02/1.22  ----------------------
% 2.02/1.22  Preprocessing        : 0.29
% 2.02/1.22  Parsing              : 0.16
% 2.02/1.22  CNF conversion       : 0.02
% 2.02/1.22  Main loop            : 0.17
% 2.02/1.22  Inferencing          : 0.06
% 2.02/1.22  Reduction            : 0.05
% 2.02/1.22  Demodulation         : 0.04
% 2.02/1.22  BG Simplification    : 0.01
% 2.02/1.22  Subsumption          : 0.03
% 2.02/1.22  Abstraction          : 0.01
% 2.02/1.22  MUC search           : 0.00
% 2.02/1.22  Cooper               : 0.00
% 2.02/1.22  Total                : 0.48
% 2.02/1.22  Index Insertion      : 0.00
% 2.02/1.22  Index Deletion       : 0.00
% 2.02/1.22  Index Matching       : 0.00
% 2.02/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
