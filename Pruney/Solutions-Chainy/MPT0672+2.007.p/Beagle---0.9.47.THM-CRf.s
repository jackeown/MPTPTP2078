%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:22 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   24 (  32 expanded)
%              Number of leaves         :   13 (  18 expanded)
%              Depth                    :    4
%              Number of atoms          :   29 (  58 expanded)
%              Number of equality atoms :   10 (  22 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k8_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r1_tarski(A,B)
         => ( k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C)
            & k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(A,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_funct_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).

tff(c_12,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6] :
      ( k8_relat_1(A_4,k8_relat_1(B_5,C_6)) = k8_relat_1(A_4,C_6)
      | ~ r1_tarski(A_4,B_5)
      | ~ v1_relat_1(C_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1,C_3] :
      ( k8_relat_1(B_2,k8_relat_1(A_1,C_3)) = k8_relat_1(A_1,C_3)
      | ~ r1_tarski(A_1,B_2)
      | ~ v1_relat_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,
    ( k8_relat_1('#skF_1',k8_relat_1('#skF_2','#skF_3')) != k8_relat_1('#skF_1','#skF_3')
    | k8_relat_1('#skF_2',k8_relat_1('#skF_1','#skF_3')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_56,plain,(
    k8_relat_1('#skF_2',k8_relat_1('#skF_1','#skF_3')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_6])).

tff(c_62,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_56])).

tff(c_68,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_8,c_62])).

tff(c_69,plain,(
    k8_relat_1('#skF_1',k8_relat_1('#skF_2','#skF_3')) != k8_relat_1('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_6])).

tff(c_73,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_69])).

tff(c_80,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_8,c_73])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:37:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.30  
% 1.80/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.30  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k8_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.80/1.30  
% 1.80/1.30  %Foreground sorts:
% 1.80/1.30  
% 1.80/1.30  
% 1.80/1.30  %Background operators:
% 1.80/1.30  
% 1.80/1.30  
% 1.80/1.30  %Foreground operators:
% 1.80/1.30  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.80/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.80/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.80/1.30  tff('#skF_2', type, '#skF_2': $i).
% 1.80/1.30  tff('#skF_3', type, '#skF_3': $i).
% 1.80/1.30  tff('#skF_1', type, '#skF_1': $i).
% 1.80/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.80/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.30  
% 1.97/1.31  tff(f_48, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r1_tarski(A, B) => ((k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C)) & (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(A, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_funct_1)).
% 1.97/1.31  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_relat_1)).
% 1.97/1.31  tff(f_31, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_relat_1)).
% 1.97/1.31  tff(c_12, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.97/1.31  tff(c_8, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.97/1.31  tff(c_4, plain, (![A_4, B_5, C_6]: (k8_relat_1(A_4, k8_relat_1(B_5, C_6))=k8_relat_1(A_4, C_6) | ~r1_tarski(A_4, B_5) | ~v1_relat_1(C_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.97/1.31  tff(c_2, plain, (![B_2, A_1, C_3]: (k8_relat_1(B_2, k8_relat_1(A_1, C_3))=k8_relat_1(A_1, C_3) | ~r1_tarski(A_1, B_2) | ~v1_relat_1(C_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.97/1.31  tff(c_6, plain, (k8_relat_1('#skF_1', k8_relat_1('#skF_2', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3') | k8_relat_1('#skF_2', k8_relat_1('#skF_1', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.97/1.31  tff(c_56, plain, (k8_relat_1('#skF_2', k8_relat_1('#skF_1', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_6])).
% 1.97/1.31  tff(c_62, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2, c_56])).
% 1.97/1.31  tff(c_68, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_8, c_62])).
% 1.97/1.31  tff(c_69, plain, (k8_relat_1('#skF_1', k8_relat_1('#skF_2', '#skF_3'))!=k8_relat_1('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_6])).
% 1.97/1.31  tff(c_73, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4, c_69])).
% 1.97/1.31  tff(c_80, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_8, c_73])).
% 1.97/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.31  
% 1.97/1.31  Inference rules
% 1.97/1.31  ----------------------
% 1.97/1.31  #Ref     : 0
% 1.97/1.31  #Sup     : 16
% 1.97/1.31  #Fact    : 0
% 1.97/1.31  #Define  : 0
% 1.97/1.31  #Split   : 1
% 1.97/1.31  #Chain   : 0
% 1.97/1.31  #Close   : 0
% 1.97/1.31  
% 1.97/1.31  Ordering : KBO
% 1.97/1.31  
% 1.97/1.31  Simplification rules
% 1.97/1.31  ----------------------
% 1.97/1.31  #Subsume      : 0
% 1.97/1.31  #Demod        : 5
% 1.97/1.31  #Tautology    : 5
% 1.97/1.31  #SimpNegUnit  : 0
% 1.97/1.31  #BackRed      : 0
% 1.97/1.31  
% 1.97/1.31  #Partial instantiations: 0
% 1.97/1.31  #Strategies tried      : 1
% 1.97/1.31  
% 1.97/1.31  Timing (in seconds)
% 1.97/1.31  ----------------------
% 1.97/1.31  Preprocessing        : 0.33
% 1.97/1.32  Parsing              : 0.19
% 1.97/1.32  CNF conversion       : 0.02
% 1.97/1.32  Main loop            : 0.13
% 1.97/1.32  Inferencing          : 0.06
% 1.97/1.32  Reduction            : 0.03
% 1.97/1.32  Demodulation         : 0.02
% 1.97/1.32  BG Simplification    : 0.01
% 1.97/1.32  Subsumption          : 0.02
% 1.97/1.32  Abstraction          : 0.01
% 1.97/1.32  MUC search           : 0.00
% 1.97/1.32  Cooper               : 0.00
% 1.97/1.32  Total                : 0.49
% 1.97/1.32  Index Insertion      : 0.00
% 1.97/1.32  Index Deletion       : 0.00
% 1.97/1.32  Index Matching       : 0.00
% 1.97/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
