%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:33 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   33 (  37 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   45 (  61 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_xboole_0(B,C)
           => r1_xboole_0(k10_relat_1(A,B),k10_relat_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t141_funct_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_20,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_18,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_64,plain,(
    ! [C_39,A_40,B_41] :
      ( k3_xboole_0(k10_relat_1(C_39,A_40),k10_relat_1(C_39,B_41)) = k10_relat_1(C_39,k3_xboole_0(A_40,B_41))
      | ~ v1_funct_1(C_39)
      | ~ v1_relat_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),k3_xboole_0(A_1,B_2))
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_184,plain,(
    ! [C_87,A_88,B_89] :
      ( r2_hidden('#skF_1'(k10_relat_1(C_87,A_88),k10_relat_1(C_87,B_89)),k10_relat_1(C_87,k3_xboole_0(A_88,B_89)))
      | r1_xboole_0(k10_relat_1(C_87,A_88),k10_relat_1(C_87,B_89))
      | ~ v1_funct_1(C_87)
      | ~ v1_relat_1(C_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_2])).

tff(c_29,plain,(
    ! [A_22,B_23,C_24] :
      ( r2_hidden('#skF_2'(A_22,B_23,C_24),B_23)
      | ~ r2_hidden(A_22,k10_relat_1(C_24,B_23))
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_34,plain,(
    ! [A_1,B_2,A_22,C_24] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(A_22,k10_relat_1(C_24,k3_xboole_0(A_1,B_2)))
      | ~ v1_relat_1(C_24) ) ),
    inference(resolution,[status(thm)],[c_29,c_4])).

tff(c_210,plain,(
    ! [A_90,B_91,C_92] :
      ( ~ r1_xboole_0(A_90,B_91)
      | r1_xboole_0(k10_relat_1(C_92,A_90),k10_relat_1(C_92,B_91))
      | ~ v1_funct_1(C_92)
      | ~ v1_relat_1(C_92) ) ),
    inference(resolution,[status(thm)],[c_184,c_34])).

tff(c_16,plain,(
    ~ r1_xboole_0(k10_relat_1('#skF_3','#skF_4'),k10_relat_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_217,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_210,c_16])).

tff(c_223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_18,c_217])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:33:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.37  
% 2.54/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.38  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 2.54/1.38  
% 2.54/1.38  %Foreground sorts:
% 2.54/1.38  
% 2.54/1.38  
% 2.54/1.38  %Background operators:
% 2.54/1.38  
% 2.54/1.38  
% 2.54/1.38  %Foreground operators:
% 2.54/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.54/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.54/1.38  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.54/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.54/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.54/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.54/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.54/1.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.54/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.38  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.54/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.54/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.54/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.54/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.54/1.38  
% 2.54/1.39  tff(f_66, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_xboole_0(B, C) => r1_xboole_0(k10_relat_1(A, B), k10_relat_1(A, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t141_funct_1)).
% 2.54/1.39  tff(f_56, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_funct_1)).
% 2.54/1.39  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.54/1.39  tff(f_50, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 2.54/1.39  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.54/1.39  tff(c_20, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.54/1.39  tff(c_18, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.54/1.39  tff(c_64, plain, (![C_39, A_40, B_41]: (k3_xboole_0(k10_relat_1(C_39, A_40), k10_relat_1(C_39, B_41))=k10_relat_1(C_39, k3_xboole_0(A_40, B_41)) | ~v1_funct_1(C_39) | ~v1_relat_1(C_39))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.54/1.39  tff(c_2, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), k3_xboole_0(A_1, B_2)) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.54/1.39  tff(c_184, plain, (![C_87, A_88, B_89]: (r2_hidden('#skF_1'(k10_relat_1(C_87, A_88), k10_relat_1(C_87, B_89)), k10_relat_1(C_87, k3_xboole_0(A_88, B_89))) | r1_xboole_0(k10_relat_1(C_87, A_88), k10_relat_1(C_87, B_89)) | ~v1_funct_1(C_87) | ~v1_relat_1(C_87))), inference(superposition, [status(thm), theory('equality')], [c_64, c_2])).
% 2.54/1.39  tff(c_29, plain, (![A_22, B_23, C_24]: (r2_hidden('#skF_2'(A_22, B_23, C_24), B_23) | ~r2_hidden(A_22, k10_relat_1(C_24, B_23)) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.54/1.39  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.54/1.39  tff(c_34, plain, (![A_1, B_2, A_22, C_24]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(A_22, k10_relat_1(C_24, k3_xboole_0(A_1, B_2))) | ~v1_relat_1(C_24))), inference(resolution, [status(thm)], [c_29, c_4])).
% 2.54/1.39  tff(c_210, plain, (![A_90, B_91, C_92]: (~r1_xboole_0(A_90, B_91) | r1_xboole_0(k10_relat_1(C_92, A_90), k10_relat_1(C_92, B_91)) | ~v1_funct_1(C_92) | ~v1_relat_1(C_92))), inference(resolution, [status(thm)], [c_184, c_34])).
% 2.54/1.39  tff(c_16, plain, (~r1_xboole_0(k10_relat_1('#skF_3', '#skF_4'), k10_relat_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.54/1.39  tff(c_217, plain, (~r1_xboole_0('#skF_4', '#skF_5') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_210, c_16])).
% 2.54/1.39  tff(c_223, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_18, c_217])).
% 2.54/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.39  
% 2.54/1.39  Inference rules
% 2.54/1.39  ----------------------
% 2.54/1.39  #Ref     : 0
% 2.54/1.39  #Sup     : 44
% 2.54/1.39  #Fact    : 0
% 2.54/1.39  #Define  : 0
% 2.54/1.39  #Split   : 0
% 2.54/1.39  #Chain   : 0
% 2.54/1.39  #Close   : 0
% 2.54/1.39  
% 2.54/1.39  Ordering : KBO
% 2.54/1.39  
% 2.54/1.39  Simplification rules
% 2.54/1.39  ----------------------
% 2.54/1.39  #Subsume      : 1
% 2.54/1.39  #Demod        : 3
% 2.54/1.39  #Tautology    : 3
% 2.54/1.39  #SimpNegUnit  : 0
% 2.54/1.39  #BackRed      : 0
% 2.54/1.39  
% 2.54/1.39  #Partial instantiations: 0
% 2.54/1.39  #Strategies tried      : 1
% 2.54/1.39  
% 2.54/1.39  Timing (in seconds)
% 2.54/1.39  ----------------------
% 2.54/1.39  Preprocessing        : 0.32
% 2.54/1.39  Parsing              : 0.18
% 2.54/1.39  CNF conversion       : 0.02
% 2.54/1.39  Main loop            : 0.29
% 2.54/1.39  Inferencing          : 0.12
% 2.54/1.39  Reduction            : 0.05
% 2.54/1.39  Demodulation         : 0.04
% 2.54/1.39  BG Simplification    : 0.02
% 2.54/1.39  Subsumption          : 0.08
% 2.54/1.39  Abstraction          : 0.01
% 2.54/1.39  MUC search           : 0.00
% 2.54/1.39  Cooper               : 0.00
% 2.54/1.39  Total                : 0.64
% 2.54/1.39  Index Insertion      : 0.00
% 2.54/1.39  Index Deletion       : 0.00
% 2.54/1.39  Index Matching       : 0.00
% 2.54/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
