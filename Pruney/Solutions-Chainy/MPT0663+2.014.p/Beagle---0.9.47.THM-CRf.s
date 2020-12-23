%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:13 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   38 (  43 expanded)
%              Number of leaves         :   27 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   28 (  45 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
         => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
       => k1_funct_1(C,A) = k1_funct_1(k5_relat_1(k6_relat_1(B),C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_1)).

tff(c_22,plain,(
    k1_funct_1(k7_relat_1('#skF_3','#skF_2'),'#skF_1') != k1_funct_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_18,plain,(
    ! [A_32,B_33] :
      ( k5_relat_1(k6_relat_1(A_32),B_33) = k7_relat_1(B_33,A_32)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_26,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_24,plain,(
    r2_hidden('#skF_1',k3_xboole_0(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_278,plain,(
    ! [B_80,C_81,A_82] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(B_80),C_81),A_82) = k1_funct_1(C_81,A_82)
      | ~ r2_hidden(A_82,k3_xboole_0(k1_relat_1(C_81),B_80))
      | ~ v1_funct_1(C_81)
      | ~ v1_relat_1(C_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_281,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1('#skF_2'),'#skF_3'),'#skF_1') = k1_funct_1('#skF_3','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_278])).

tff(c_284,plain,(
    k1_funct_1(k5_relat_1(k6_relat_1('#skF_2'),'#skF_3'),'#skF_1') = k1_funct_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_281])).

tff(c_289,plain,
    ( k1_funct_1(k7_relat_1('#skF_3','#skF_2'),'#skF_1') = k1_funct_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_284])).

tff(c_293,plain,(
    k1_funct_1(k7_relat_1('#skF_3','#skF_2'),'#skF_1') = k1_funct_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_289])).

tff(c_295,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_293])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:13:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.24  
% 2.03/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.24  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.17/1.24  
% 2.17/1.24  %Foreground sorts:
% 2.17/1.24  
% 2.17/1.24  
% 2.17/1.24  %Background operators:
% 2.17/1.24  
% 2.17/1.24  
% 2.17/1.24  %Foreground operators:
% 2.17/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.17/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.17/1.24  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.17/1.24  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.17/1.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.17/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.17/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.17/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.17/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.24  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.17/1.24  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.17/1.24  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.17/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.17/1.24  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.17/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.17/1.24  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.17/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.17/1.24  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.17/1.24  
% 2.19/1.25  tff(f_62, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_funct_1)).
% 2.19/1.25  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.19/1.25  tff(f_53, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(C, A) = k1_funct_1(k5_relat_1(k6_relat_1(B), C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_1)).
% 2.19/1.25  tff(c_22, plain, (k1_funct_1(k7_relat_1('#skF_3', '#skF_2'), '#skF_1')!=k1_funct_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.19/1.25  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.19/1.25  tff(c_18, plain, (![A_32, B_33]: (k5_relat_1(k6_relat_1(A_32), B_33)=k7_relat_1(B_33, A_32) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.19/1.25  tff(c_26, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.19/1.25  tff(c_24, plain, (r2_hidden('#skF_1', k3_xboole_0(k1_relat_1('#skF_3'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.19/1.25  tff(c_278, plain, (![B_80, C_81, A_82]: (k1_funct_1(k5_relat_1(k6_relat_1(B_80), C_81), A_82)=k1_funct_1(C_81, A_82) | ~r2_hidden(A_82, k3_xboole_0(k1_relat_1(C_81), B_80)) | ~v1_funct_1(C_81) | ~v1_relat_1(C_81))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.19/1.25  tff(c_281, plain, (k1_funct_1(k5_relat_1(k6_relat_1('#skF_2'), '#skF_3'), '#skF_1')=k1_funct_1('#skF_3', '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_278])).
% 2.19/1.25  tff(c_284, plain, (k1_funct_1(k5_relat_1(k6_relat_1('#skF_2'), '#skF_3'), '#skF_1')=k1_funct_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_281])).
% 2.19/1.25  tff(c_289, plain, (k1_funct_1(k7_relat_1('#skF_3', '#skF_2'), '#skF_1')=k1_funct_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18, c_284])).
% 2.19/1.25  tff(c_293, plain, (k1_funct_1(k7_relat_1('#skF_3', '#skF_2'), '#skF_1')=k1_funct_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_289])).
% 2.19/1.25  tff(c_295, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_293])).
% 2.19/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.25  
% 2.19/1.25  Inference rules
% 2.19/1.25  ----------------------
% 2.19/1.25  #Ref     : 0
% 2.19/1.25  #Sup     : 65
% 2.19/1.25  #Fact    : 0
% 2.19/1.25  #Define  : 0
% 2.19/1.25  #Split   : 0
% 2.19/1.25  #Chain   : 0
% 2.19/1.25  #Close   : 0
% 2.19/1.25  
% 2.19/1.25  Ordering : KBO
% 2.19/1.25  
% 2.19/1.25  Simplification rules
% 2.19/1.25  ----------------------
% 2.19/1.25  #Subsume      : 0
% 2.19/1.25  #Demod        : 25
% 2.19/1.25  #Tautology    : 48
% 2.19/1.25  #SimpNegUnit  : 1
% 2.19/1.25  #BackRed      : 0
% 2.19/1.25  
% 2.19/1.25  #Partial instantiations: 0
% 2.19/1.25  #Strategies tried      : 1
% 2.19/1.25  
% 2.19/1.25  Timing (in seconds)
% 2.19/1.25  ----------------------
% 2.19/1.25  Preprocessing        : 0.31
% 2.19/1.25  Parsing              : 0.17
% 2.19/1.25  CNF conversion       : 0.02
% 2.19/1.25  Main loop            : 0.19
% 2.19/1.25  Inferencing          : 0.08
% 2.19/1.25  Reduction            : 0.07
% 2.19/1.25  Demodulation         : 0.05
% 2.19/1.25  BG Simplification    : 0.01
% 2.19/1.25  Subsumption          : 0.02
% 2.19/1.25  Abstraction          : 0.02
% 2.19/1.25  MUC search           : 0.00
% 2.19/1.25  Cooper               : 0.00
% 2.19/1.25  Total                : 0.52
% 2.19/1.25  Index Insertion      : 0.00
% 2.19/1.25  Index Deletion       : 0.00
% 2.19/1.25  Index Matching       : 0.00
% 2.19/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
