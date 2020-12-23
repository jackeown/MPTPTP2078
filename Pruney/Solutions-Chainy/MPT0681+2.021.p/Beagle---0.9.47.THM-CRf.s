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
% DateTime   : Thu Dec  3 10:04:28 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   39 (  44 expanded)
%              Number of leaves         :   25 (  30 expanded)
%              Depth                    :    5
%              Number of atoms          :   52 (  76 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_xboole_0(A,B)
            & v2_funct_1(C) )
         => r1_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_funct_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_28,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_24,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_26,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_99,plain,(
    ! [C_51,A_52,B_53] :
      ( k3_xboole_0(k9_relat_1(C_51,A_52),k9_relat_1(C_51,B_53)) = k9_relat_1(C_51,k3_xboole_0(A_52,B_53))
      | ~ v2_funct_1(C_51)
      | ~ v1_funct_1(C_51)
      | ~ v1_relat_1(C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),k3_xboole_0(A_1,B_2))
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_248,plain,(
    ! [C_116,A_117,B_118] :
      ( r2_hidden('#skF_1'(k9_relat_1(C_116,A_117),k9_relat_1(C_116,B_118)),k9_relat_1(C_116,k3_xboole_0(A_117,B_118)))
      | r1_xboole_0(k9_relat_1(C_116,A_117),k9_relat_1(C_116,B_118))
      | ~ v2_funct_1(C_116)
      | ~ v1_funct_1(C_116)
      | ~ v1_relat_1(C_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_2])).

tff(c_64,plain,(
    ! [A_34,B_35,C_36] :
      ( r2_hidden('#skF_2'(A_34,B_35,C_36),B_35)
      | ~ r2_hidden(A_34,k9_relat_1(C_36,B_35))
      | ~ v1_relat_1(C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_69,plain,(
    ! [A_1,B_2,A_34,C_36] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(A_34,k9_relat_1(C_36,k3_xboole_0(A_1,B_2)))
      | ~ v1_relat_1(C_36) ) ),
    inference(resolution,[status(thm)],[c_64,c_4])).

tff(c_293,plain,(
    ! [A_125,B_126,C_127] :
      ( ~ r1_xboole_0(A_125,B_126)
      | r1_xboole_0(k9_relat_1(C_127,A_125),k9_relat_1(C_127,B_126))
      | ~ v2_funct_1(C_127)
      | ~ v1_funct_1(C_127)
      | ~ v1_relat_1(C_127) ) ),
    inference(resolution,[status(thm)],[c_248,c_69])).

tff(c_22,plain,(
    ~ r1_xboole_0(k9_relat_1('#skF_5','#skF_3'),k9_relat_1('#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_300,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_293,c_22])).

tff(c_306,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_24,c_26,c_300])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:22:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.43  
% 2.57/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.43  %$ r2_hidden > r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 2.57/1.43  
% 2.57/1.43  %Foreground sorts:
% 2.57/1.43  
% 2.57/1.43  
% 2.57/1.43  %Background operators:
% 2.57/1.43  
% 2.57/1.43  
% 2.57/1.43  %Foreground operators:
% 2.57/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.57/1.43  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.57/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.57/1.43  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.57/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.57/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.57/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.57/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.57/1.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.57/1.43  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.57/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.57/1.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.57/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.57/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.57/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.57/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.57/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.57/1.43  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.57/1.43  
% 2.57/1.44  tff(f_75, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_xboole_0(A, B) & v2_funct_1(C)) => r1_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_funct_1)).
% 2.57/1.44  tff(f_64, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_1)).
% 2.57/1.44  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.57/1.44  tff(f_56, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 2.57/1.44  tff(c_30, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.57/1.44  tff(c_28, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.57/1.44  tff(c_24, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.57/1.44  tff(c_26, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.57/1.44  tff(c_99, plain, (![C_51, A_52, B_53]: (k3_xboole_0(k9_relat_1(C_51, A_52), k9_relat_1(C_51, B_53))=k9_relat_1(C_51, k3_xboole_0(A_52, B_53)) | ~v2_funct_1(C_51) | ~v1_funct_1(C_51) | ~v1_relat_1(C_51))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.57/1.44  tff(c_2, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), k3_xboole_0(A_1, B_2)) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.57/1.44  tff(c_248, plain, (![C_116, A_117, B_118]: (r2_hidden('#skF_1'(k9_relat_1(C_116, A_117), k9_relat_1(C_116, B_118)), k9_relat_1(C_116, k3_xboole_0(A_117, B_118))) | r1_xboole_0(k9_relat_1(C_116, A_117), k9_relat_1(C_116, B_118)) | ~v2_funct_1(C_116) | ~v1_funct_1(C_116) | ~v1_relat_1(C_116))), inference(superposition, [status(thm), theory('equality')], [c_99, c_2])).
% 2.57/1.44  tff(c_64, plain, (![A_34, B_35, C_36]: (r2_hidden('#skF_2'(A_34, B_35, C_36), B_35) | ~r2_hidden(A_34, k9_relat_1(C_36, B_35)) | ~v1_relat_1(C_36))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.57/1.44  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.57/1.44  tff(c_69, plain, (![A_1, B_2, A_34, C_36]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(A_34, k9_relat_1(C_36, k3_xboole_0(A_1, B_2))) | ~v1_relat_1(C_36))), inference(resolution, [status(thm)], [c_64, c_4])).
% 2.57/1.44  tff(c_293, plain, (![A_125, B_126, C_127]: (~r1_xboole_0(A_125, B_126) | r1_xboole_0(k9_relat_1(C_127, A_125), k9_relat_1(C_127, B_126)) | ~v2_funct_1(C_127) | ~v1_funct_1(C_127) | ~v1_relat_1(C_127))), inference(resolution, [status(thm)], [c_248, c_69])).
% 2.57/1.44  tff(c_22, plain, (~r1_xboole_0(k9_relat_1('#skF_5', '#skF_3'), k9_relat_1('#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.57/1.44  tff(c_300, plain, (~r1_xboole_0('#skF_3', '#skF_4') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_293, c_22])).
% 2.57/1.44  tff(c_306, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_24, c_26, c_300])).
% 2.57/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.44  
% 2.57/1.44  Inference rules
% 2.57/1.44  ----------------------
% 2.57/1.44  #Ref     : 0
% 2.57/1.44  #Sup     : 60
% 2.57/1.44  #Fact    : 0
% 2.57/1.44  #Define  : 0
% 2.57/1.44  #Split   : 0
% 2.57/1.44  #Chain   : 0
% 2.57/1.44  #Close   : 0
% 2.57/1.44  
% 2.57/1.44  Ordering : KBO
% 2.57/1.44  
% 2.57/1.44  Simplification rules
% 2.57/1.44  ----------------------
% 2.57/1.44  #Subsume      : 1
% 2.57/1.44  #Demod        : 4
% 2.57/1.44  #Tautology    : 9
% 2.57/1.44  #SimpNegUnit  : 0
% 2.57/1.44  #BackRed      : 0
% 2.57/1.44  
% 2.57/1.44  #Partial instantiations: 0
% 2.57/1.44  #Strategies tried      : 1
% 2.57/1.44  
% 2.57/1.44  Timing (in seconds)
% 2.57/1.44  ----------------------
% 2.57/1.44  Preprocessing        : 0.31
% 2.57/1.44  Parsing              : 0.16
% 2.57/1.44  CNF conversion       : 0.02
% 2.57/1.44  Main loop            : 0.35
% 2.57/1.44  Inferencing          : 0.14
% 2.57/1.44  Reduction            : 0.06
% 2.57/1.44  Demodulation         : 0.05
% 2.57/1.44  BG Simplification    : 0.02
% 2.57/1.44  Subsumption          : 0.11
% 2.57/1.44  Abstraction          : 0.02
% 2.57/1.44  MUC search           : 0.00
% 2.57/1.44  Cooper               : 0.00
% 2.57/1.44  Total                : 0.69
% 2.57/1.44  Index Insertion      : 0.00
% 2.57/1.44  Index Deletion       : 0.00
% 2.57/1.45  Index Matching       : 0.00
% 2.57/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
