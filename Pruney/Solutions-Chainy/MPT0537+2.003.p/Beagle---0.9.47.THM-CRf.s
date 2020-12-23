%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:20 EST 2020

% Result     : Theorem 8.93s
% Output     : CNFRefutation 8.93s
% Verified   : 
% Statistics : Number of formulae       :   40 (  45 expanded)
%              Number of leaves         :   25 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   53 (  71 expanded)
%              Number of equality atoms :   14 (  18 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k8_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_7 > #skF_1 > #skF_6 > #skF_8 > #skF_4 > #skF_5 > #skF_2 > #skF_9 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k8_relat_1(k1_xboole_0,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( C = k8_relat_1(A,B)
          <=> ! [D,E] :
                ( r2_hidden(k4_tarski(D,E),C)
              <=> ( r2_hidden(E,A)
                  & r2_hidden(k4_tarski(D,E),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_52,plain,(
    k8_relat_1(k1_xboole_0,'#skF_9') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_54,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_46,plain,(
    ! [A_30,B_31] :
      ( v1_relat_1(k8_relat_1(A_30,B_31))
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_50,plain,(
    ! [A_35] :
      ( k1_xboole_0 = A_35
      | r2_hidden(k4_tarski('#skF_7'(A_35),'#skF_8'(A_35)),A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_389,plain,(
    ! [E_78,A_79,D_80,B_81] :
      ( r2_hidden(E_78,A_79)
      | ~ r2_hidden(k4_tarski(D_80,E_78),k8_relat_1(A_79,B_81))
      | ~ v1_relat_1(k8_relat_1(A_79,B_81))
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_397,plain,(
    ! [A_79,B_81] :
      ( r2_hidden('#skF_8'(k8_relat_1(A_79,B_81)),A_79)
      | ~ v1_relat_1(B_81)
      | k8_relat_1(A_79,B_81) = k1_xboole_0
      | ~ v1_relat_1(k8_relat_1(A_79,B_81)) ) ),
    inference(resolution,[status(thm)],[c_50,c_389])).

tff(c_4747,plain,(
    ! [A_253,B_254] :
      ( r2_hidden('#skF_8'(k8_relat_1(A_253,B_254)),A_253)
      | ~ v1_relat_1(B_254)
      | k8_relat_1(A_253,B_254) = k1_xboole_0
      | ~ v1_relat_1(k8_relat_1(A_253,B_254)) ) ),
    inference(resolution,[status(thm)],[c_50,c_389])).

tff(c_22,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_89,plain,(
    ! [D_43,B_44,A_45] :
      ( ~ r2_hidden(D_43,B_44)
      | ~ r2_hidden(D_43,k4_xboole_0(A_45,B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_95,plain,(
    ! [D_43,A_8] :
      ( ~ r2_hidden(D_43,k1_xboole_0)
      | ~ r2_hidden(D_43,A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_89])).

tff(c_12760,plain,(
    ! [B_423,A_424] :
      ( ~ r2_hidden('#skF_8'(k8_relat_1(k1_xboole_0,B_423)),A_424)
      | ~ v1_relat_1(B_423)
      | k8_relat_1(k1_xboole_0,B_423) = k1_xboole_0
      | ~ v1_relat_1(k8_relat_1(k1_xboole_0,B_423)) ) ),
    inference(resolution,[status(thm)],[c_4747,c_95])).

tff(c_12809,plain,(
    ! [B_425] :
      ( ~ v1_relat_1(B_425)
      | k8_relat_1(k1_xboole_0,B_425) = k1_xboole_0
      | ~ v1_relat_1(k8_relat_1(k1_xboole_0,B_425)) ) ),
    inference(resolution,[status(thm)],[c_397,c_12760])).

tff(c_12853,plain,(
    ! [B_426] :
      ( k8_relat_1(k1_xboole_0,B_426) = k1_xboole_0
      | ~ v1_relat_1(B_426) ) ),
    inference(resolution,[status(thm)],[c_46,c_12809])).

tff(c_12868,plain,(
    k8_relat_1(k1_xboole_0,'#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_12853])).

tff(c_12876,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_12868])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:33:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.93/2.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.93/2.95  
% 8.93/2.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.93/2.95  %$ r2_hidden > v1_relat_1 > k8_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_7 > #skF_1 > #skF_6 > #skF_8 > #skF_4 > #skF_5 > #skF_2 > #skF_9 > #skF_3
% 8.93/2.95  
% 8.93/2.95  %Foreground sorts:
% 8.93/2.95  
% 8.93/2.95  
% 8.93/2.95  %Background operators:
% 8.93/2.95  
% 8.93/2.95  
% 8.93/2.95  %Foreground operators:
% 8.93/2.95  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 8.93/2.95  tff('#skF_7', type, '#skF_7': $i > $i).
% 8.93/2.95  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.93/2.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.93/2.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.93/2.95  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 8.93/2.95  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.93/2.95  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.93/2.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.93/2.95  tff('#skF_8', type, '#skF_8': $i > $i).
% 8.93/2.95  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 8.93/2.95  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 8.93/2.95  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.93/2.95  tff('#skF_9', type, '#skF_9': $i).
% 8.93/2.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.93/2.95  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.93/2.95  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.93/2.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.93/2.95  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.93/2.95  
% 8.93/2.96  tff(f_78, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k8_relat_1(k1_xboole_0, A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_relat_1)).
% 8.93/2.96  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 8.93/2.96  tff(f_73, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 8.93/2.96  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k8_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (r2_hidden(E, A) & r2_hidden(k4_tarski(D, E), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_relat_1)).
% 8.93/2.96  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 8.93/2.96  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 8.93/2.96  tff(c_52, plain, (k8_relat_1(k1_xboole_0, '#skF_9')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.93/2.96  tff(c_54, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.93/2.96  tff(c_46, plain, (![A_30, B_31]: (v1_relat_1(k8_relat_1(A_30, B_31)) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.93/2.96  tff(c_50, plain, (![A_35]: (k1_xboole_0=A_35 | r2_hidden(k4_tarski('#skF_7'(A_35), '#skF_8'(A_35)), A_35) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.93/2.96  tff(c_389, plain, (![E_78, A_79, D_80, B_81]: (r2_hidden(E_78, A_79) | ~r2_hidden(k4_tarski(D_80, E_78), k8_relat_1(A_79, B_81)) | ~v1_relat_1(k8_relat_1(A_79, B_81)) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.93/2.96  tff(c_397, plain, (![A_79, B_81]: (r2_hidden('#skF_8'(k8_relat_1(A_79, B_81)), A_79) | ~v1_relat_1(B_81) | k8_relat_1(A_79, B_81)=k1_xboole_0 | ~v1_relat_1(k8_relat_1(A_79, B_81)))), inference(resolution, [status(thm)], [c_50, c_389])).
% 8.93/2.96  tff(c_4747, plain, (![A_253, B_254]: (r2_hidden('#skF_8'(k8_relat_1(A_253, B_254)), A_253) | ~v1_relat_1(B_254) | k8_relat_1(A_253, B_254)=k1_xboole_0 | ~v1_relat_1(k8_relat_1(A_253, B_254)))), inference(resolution, [status(thm)], [c_50, c_389])).
% 8.93/2.96  tff(c_22, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.93/2.96  tff(c_89, plain, (![D_43, B_44, A_45]: (~r2_hidden(D_43, B_44) | ~r2_hidden(D_43, k4_xboole_0(A_45, B_44)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.93/2.96  tff(c_95, plain, (![D_43, A_8]: (~r2_hidden(D_43, k1_xboole_0) | ~r2_hidden(D_43, A_8))), inference(superposition, [status(thm), theory('equality')], [c_22, c_89])).
% 8.93/2.96  tff(c_12760, plain, (![B_423, A_424]: (~r2_hidden('#skF_8'(k8_relat_1(k1_xboole_0, B_423)), A_424) | ~v1_relat_1(B_423) | k8_relat_1(k1_xboole_0, B_423)=k1_xboole_0 | ~v1_relat_1(k8_relat_1(k1_xboole_0, B_423)))), inference(resolution, [status(thm)], [c_4747, c_95])).
% 8.93/2.96  tff(c_12809, plain, (![B_425]: (~v1_relat_1(B_425) | k8_relat_1(k1_xboole_0, B_425)=k1_xboole_0 | ~v1_relat_1(k8_relat_1(k1_xboole_0, B_425)))), inference(resolution, [status(thm)], [c_397, c_12760])).
% 8.93/2.96  tff(c_12853, plain, (![B_426]: (k8_relat_1(k1_xboole_0, B_426)=k1_xboole_0 | ~v1_relat_1(B_426))), inference(resolution, [status(thm)], [c_46, c_12809])).
% 8.93/2.96  tff(c_12868, plain, (k8_relat_1(k1_xboole_0, '#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_12853])).
% 8.93/2.96  tff(c_12876, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_12868])).
% 8.93/2.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.93/2.96  
% 8.93/2.96  Inference rules
% 8.93/2.96  ----------------------
% 8.93/2.96  #Ref     : 0
% 8.93/2.96  #Sup     : 3144
% 8.93/2.96  #Fact    : 0
% 8.93/2.96  #Define  : 0
% 8.93/2.96  #Split   : 1
% 8.93/2.96  #Chain   : 0
% 8.93/2.96  #Close   : 0
% 8.93/2.96  
% 8.93/2.96  Ordering : KBO
% 8.93/2.96  
% 8.93/2.96  Simplification rules
% 8.93/2.96  ----------------------
% 8.93/2.96  #Subsume      : 909
% 8.93/2.96  #Demod        : 2828
% 8.93/2.96  #Tautology    : 1086
% 8.93/2.96  #SimpNegUnit  : 1
% 8.93/2.96  #BackRed      : 1
% 8.93/2.96  
% 8.93/2.96  #Partial instantiations: 0
% 8.93/2.96  #Strategies tried      : 1
% 8.93/2.96  
% 8.93/2.96  Timing (in seconds)
% 8.93/2.96  ----------------------
% 8.93/2.96  Preprocessing        : 0.30
% 8.93/2.96  Parsing              : 0.15
% 8.93/2.96  CNF conversion       : 0.03
% 8.93/2.96  Main loop            : 1.87
% 8.93/2.96  Inferencing          : 0.57
% 8.93/2.96  Reduction            : 0.65
% 8.93/2.96  Demodulation         : 0.51
% 8.93/2.96  BG Simplification    : 0.07
% 8.93/2.96  Subsumption          : 0.47
% 8.93/2.96  Abstraction          : 0.11
% 8.93/2.96  MUC search           : 0.00
% 8.93/2.96  Cooper               : 0.00
% 8.93/2.96  Total                : 2.19
% 8.93/2.96  Index Insertion      : 0.00
% 8.93/2.96  Index Deletion       : 0.00
% 8.93/2.96  Index Matching       : 0.00
% 8.93/2.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
