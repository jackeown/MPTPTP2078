%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:24 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   30 (  45 expanded)
%              Number of leaves         :   16 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   39 (  78 expanded)
%              Number of equality atoms :    1 (   2 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k8_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => r1_tarski(k9_relat_1(k8_relat_1(A,C),B),k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ! [D] :
          ( v1_relat_1(D)
         => ( ( r1_tarski(C,D)
              & r1_tarski(A,B) )
           => r1_tarski(k9_relat_1(C,A),k9_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(k8_relat_1(A_5,B_6),B_6)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( v1_relat_1(k8_relat_1(A_3,B_4))
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    ! [C_21,A_22,D_23,B_24] :
      ( r1_tarski(k9_relat_1(C_21,A_22),k9_relat_1(D_23,B_24))
      | ~ r1_tarski(A_22,B_24)
      | ~ r1_tarski(C_21,D_23)
      | ~ v1_relat_1(D_23)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    ~ r1_tarski(k9_relat_1(k8_relat_1('#skF_1','#skF_3'),'#skF_2'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_37,plain,
    ( ~ r1_tarski('#skF_2','#skF_2')
    | ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_14])).

tff(c_42,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_6,c_37])).

tff(c_44,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_47,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_44])).

tff(c_51,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_47])).

tff(c_52,plain,(
    ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_56,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_52])).

tff(c_60,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:28:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.30  
% 1.82/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.30  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k8_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.82/1.30  
% 1.82/1.30  %Foreground sorts:
% 1.82/1.30  
% 1.82/1.30  
% 1.82/1.30  %Background operators:
% 1.82/1.30  
% 1.82/1.30  
% 1.82/1.30  %Foreground operators:
% 1.82/1.30  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.82/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.82/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.82/1.30  tff('#skF_2', type, '#skF_2': $i).
% 1.82/1.30  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.82/1.30  tff('#skF_3', type, '#skF_3': $i).
% 1.82/1.30  tff('#skF_1', type, '#skF_1': $i).
% 1.82/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.82/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.30  
% 1.82/1.31  tff(f_57, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => r1_tarski(k9_relat_1(k8_relat_1(A, C), B), k9_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_funct_1)).
% 1.82/1.31  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 1.82/1.31  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 1.82/1.31  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.82/1.31  tff(f_50, axiom, (![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k9_relat_1(C, A), k9_relat_1(D, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_relat_1)).
% 1.82/1.31  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.82/1.31  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k8_relat_1(A_5, B_6), B_6) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.82/1.31  tff(c_8, plain, (![A_3, B_4]: (v1_relat_1(k8_relat_1(A_3, B_4)) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.82/1.31  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.82/1.31  tff(c_34, plain, (![C_21, A_22, D_23, B_24]: (r1_tarski(k9_relat_1(C_21, A_22), k9_relat_1(D_23, B_24)) | ~r1_tarski(A_22, B_24) | ~r1_tarski(C_21, D_23) | ~v1_relat_1(D_23) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.82/1.31  tff(c_14, plain, (~r1_tarski(k9_relat_1(k8_relat_1('#skF_1', '#skF_3'), '#skF_2'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.82/1.31  tff(c_37, plain, (~r1_tarski('#skF_2', '#skF_2') | ~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_14])).
% 1.82/1.31  tff(c_42, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), '#skF_3') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_6, c_37])).
% 1.82/1.31  tff(c_44, plain, (~v1_relat_1(k8_relat_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_42])).
% 1.82/1.31  tff(c_47, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_44])).
% 1.82/1.31  tff(c_51, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_47])).
% 1.82/1.31  tff(c_52, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_42])).
% 1.82/1.31  tff(c_56, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_52])).
% 1.82/1.31  tff(c_60, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_56])).
% 1.82/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.31  
% 1.82/1.31  Inference rules
% 1.82/1.31  ----------------------
% 1.82/1.31  #Ref     : 0
% 1.82/1.31  #Sup     : 6
% 1.82/1.31  #Fact    : 0
% 1.82/1.31  #Define  : 0
% 1.82/1.31  #Split   : 1
% 1.82/1.31  #Chain   : 0
% 1.82/1.31  #Close   : 0
% 1.82/1.31  
% 1.82/1.31  Ordering : KBO
% 1.82/1.31  
% 1.82/1.31  Simplification rules
% 1.82/1.31  ----------------------
% 1.82/1.31  #Subsume      : 0
% 1.82/1.31  #Demod        : 6
% 1.82/1.31  #Tautology    : 2
% 1.82/1.31  #SimpNegUnit  : 0
% 1.82/1.31  #BackRed      : 0
% 1.82/1.31  
% 1.82/1.31  #Partial instantiations: 0
% 1.82/1.31  #Strategies tried      : 1
% 1.82/1.31  
% 1.82/1.31  Timing (in seconds)
% 1.82/1.31  ----------------------
% 1.82/1.32  Preprocessing        : 0.36
% 1.82/1.32  Parsing              : 0.20
% 1.82/1.32  CNF conversion       : 0.02
% 1.82/1.32  Main loop            : 0.12
% 1.82/1.32  Inferencing          : 0.05
% 1.82/1.32  Reduction            : 0.03
% 1.82/1.32  Demodulation         : 0.02
% 1.82/1.32  BG Simplification    : 0.01
% 1.82/1.32  Subsumption          : 0.02
% 1.82/1.32  Abstraction          : 0.00
% 1.82/1.32  MUC search           : 0.00
% 1.82/1.32  Cooper               : 0.00
% 1.82/1.32  Total                : 0.50
% 1.82/1.32  Index Insertion      : 0.00
% 1.82/1.32  Index Deletion       : 0.00
% 1.82/1.32  Index Matching       : 0.00
% 1.82/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
