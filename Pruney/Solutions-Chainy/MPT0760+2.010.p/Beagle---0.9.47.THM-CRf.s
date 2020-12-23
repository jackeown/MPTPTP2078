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
% DateTime   : Thu Dec  3 10:06:35 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   32 (  34 expanded)
%              Number of leaves         :   19 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   43 (  49 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k3_relat_1(B))
          | k1_wellord1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_wellord1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k1_wellord1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( D != B
                & r2_hidden(k4_tarski(D,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_28,plain,(
    k1_wellord1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_32,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_326,plain,(
    ! [A_75,B_76,C_77] :
      ( r2_hidden(k4_tarski('#skF_1'(A_75,B_76,C_77),B_76),A_75)
      | r2_hidden('#skF_2'(A_75,B_76,C_77),C_77)
      | k1_wellord1(A_75,B_76) = C_77
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [B_3,C_4,A_2] :
      ( r2_hidden(B_3,k3_relat_1(C_4))
      | ~ r2_hidden(k4_tarski(A_2,B_3),C_4)
      | ~ v1_relat_1(C_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_375,plain,(
    ! [B_78,A_79,C_80] :
      ( r2_hidden(B_78,k3_relat_1(A_79))
      | r2_hidden('#skF_2'(A_79,B_78,C_80),C_80)
      | k1_wellord1(A_79,B_78) = C_80
      | ~ v1_relat_1(A_79) ) ),
    inference(resolution,[status(thm)],[c_326,c_4])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( ~ r1_tarski(B_6,A_5)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_394,plain,(
    ! [C_81,A_82,B_83] :
      ( ~ r1_tarski(C_81,'#skF_2'(A_82,B_83,C_81))
      | r2_hidden(B_83,k3_relat_1(A_82))
      | k1_wellord1(A_82,B_83) = C_81
      | ~ v1_relat_1(A_82) ) ),
    inference(resolution,[status(thm)],[c_375,c_8])).

tff(c_399,plain,(
    ! [B_84,A_85] :
      ( r2_hidden(B_84,k3_relat_1(A_85))
      | k1_wellord1(A_85,B_84) = k1_xboole_0
      | ~ v1_relat_1(A_85) ) ),
    inference(resolution,[status(thm)],[c_2,c_394])).

tff(c_30,plain,(
    ~ r2_hidden('#skF_3',k3_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_421,plain,
    ( k1_wellord1('#skF_4','#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_399,c_30])).

tff(c_429,plain,(
    k1_wellord1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_421])).

tff(c_431,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_429])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n015.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 11:42:23 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.31  
% 2.40/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.31  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.40/1.31  
% 2.40/1.31  %Foreground sorts:
% 2.40/1.31  
% 2.40/1.31  
% 2.40/1.31  %Background operators:
% 2.40/1.31  
% 2.40/1.31  
% 2.40/1.31  %Foreground operators:
% 2.40/1.31  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.40/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.40/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.40/1.31  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.40/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.40/1.31  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.40/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.40/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.40/1.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.40/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.40/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.40/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.40/1.31  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 2.40/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.40/1.31  
% 2.40/1.32  tff(f_60, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k3_relat_1(B)) | (k1_wellord1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_wellord1)).
% 2.40/1.32  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.40/1.32  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k1_wellord1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (~(D = B) & r2_hidden(k4_tarski(D, B), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord1)).
% 2.40/1.32  tff(f_35, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relat_1)).
% 2.40/1.32  tff(f_40, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.40/1.32  tff(c_28, plain, (k1_wellord1('#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.40/1.32  tff(c_32, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.40/1.32  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.40/1.32  tff(c_326, plain, (![A_75, B_76, C_77]: (r2_hidden(k4_tarski('#skF_1'(A_75, B_76, C_77), B_76), A_75) | r2_hidden('#skF_2'(A_75, B_76, C_77), C_77) | k1_wellord1(A_75, B_76)=C_77 | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.40/1.32  tff(c_4, plain, (![B_3, C_4, A_2]: (r2_hidden(B_3, k3_relat_1(C_4)) | ~r2_hidden(k4_tarski(A_2, B_3), C_4) | ~v1_relat_1(C_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.40/1.32  tff(c_375, plain, (![B_78, A_79, C_80]: (r2_hidden(B_78, k3_relat_1(A_79)) | r2_hidden('#skF_2'(A_79, B_78, C_80), C_80) | k1_wellord1(A_79, B_78)=C_80 | ~v1_relat_1(A_79))), inference(resolution, [status(thm)], [c_326, c_4])).
% 2.40/1.32  tff(c_8, plain, (![B_6, A_5]: (~r1_tarski(B_6, A_5) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.40/1.32  tff(c_394, plain, (![C_81, A_82, B_83]: (~r1_tarski(C_81, '#skF_2'(A_82, B_83, C_81)) | r2_hidden(B_83, k3_relat_1(A_82)) | k1_wellord1(A_82, B_83)=C_81 | ~v1_relat_1(A_82))), inference(resolution, [status(thm)], [c_375, c_8])).
% 2.40/1.32  tff(c_399, plain, (![B_84, A_85]: (r2_hidden(B_84, k3_relat_1(A_85)) | k1_wellord1(A_85, B_84)=k1_xboole_0 | ~v1_relat_1(A_85))), inference(resolution, [status(thm)], [c_2, c_394])).
% 2.40/1.32  tff(c_30, plain, (~r2_hidden('#skF_3', k3_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.40/1.32  tff(c_421, plain, (k1_wellord1('#skF_4', '#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_399, c_30])).
% 2.40/1.32  tff(c_429, plain, (k1_wellord1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_421])).
% 2.40/1.32  tff(c_431, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_429])).
% 2.40/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.32  
% 2.40/1.32  Inference rules
% 2.40/1.32  ----------------------
% 2.40/1.32  #Ref     : 0
% 2.40/1.32  #Sup     : 79
% 2.40/1.32  #Fact    : 0
% 2.40/1.32  #Define  : 0
% 2.40/1.32  #Split   : 3
% 2.40/1.32  #Chain   : 0
% 2.40/1.32  #Close   : 0
% 2.40/1.32  
% 2.40/1.32  Ordering : KBO
% 2.40/1.32  
% 2.40/1.32  Simplification rules
% 2.40/1.32  ----------------------
% 2.40/1.32  #Subsume      : 15
% 2.40/1.32  #Demod        : 7
% 2.40/1.32  #Tautology    : 3
% 2.40/1.32  #SimpNegUnit  : 2
% 2.40/1.32  #BackRed      : 0
% 2.40/1.32  
% 2.40/1.32  #Partial instantiations: 0
% 2.40/1.32  #Strategies tried      : 1
% 2.40/1.32  
% 2.40/1.32  Timing (in seconds)
% 2.40/1.32  ----------------------
% 2.40/1.32  Preprocessing        : 0.26
% 2.40/1.32  Parsing              : 0.13
% 2.40/1.33  CNF conversion       : 0.02
% 2.40/1.33  Main loop            : 0.26
% 2.40/1.33  Inferencing          : 0.10
% 2.40/1.33  Reduction            : 0.06
% 2.40/1.33  Demodulation         : 0.04
% 2.40/1.33  BG Simplification    : 0.02
% 2.40/1.33  Subsumption          : 0.07
% 2.40/1.33  Abstraction          : 0.02
% 2.40/1.33  MUC search           : 0.00
% 2.40/1.33  Cooper               : 0.00
% 2.40/1.33  Total                : 0.55
% 2.40/1.33  Index Insertion      : 0.00
% 2.40/1.33  Index Deletion       : 0.00
% 2.40/1.33  Index Matching       : 0.00
% 2.40/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
