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
% DateTime   : Thu Dec  3 10:04:18 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
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
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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
         => ( k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A)
            & k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_funct_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

tff(c_12,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4,plain,(
    ! [C_6,B_5,A_4] :
      ( k7_relat_1(k7_relat_1(C_6,B_5),A_4) = k7_relat_1(C_6,A_4)
      | ~ r1_tarski(A_4,B_5)
      | ~ v1_relat_1(C_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [C_3,A_1,B_2] :
      ( k7_relat_1(k7_relat_1(C_3,A_1),B_2) = k7_relat_1(C_3,A_1)
      | ~ r1_tarski(A_1,B_2)
      | ~ v1_relat_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,
    ( k7_relat_1(k7_relat_1('#skF_3','#skF_2'),'#skF_1') != k7_relat_1('#skF_3','#skF_1')
    | k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') != k7_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_56,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') != k7_relat_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_6])).

tff(c_62,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_56])).

tff(c_68,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_8,c_62])).

tff(c_69,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_2'),'#skF_1') != k7_relat_1('#skF_3','#skF_1') ),
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
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:04:27 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.16  
% 1.66/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.16  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.66/1.16  
% 1.66/1.16  %Foreground sorts:
% 1.66/1.16  
% 1.66/1.16  
% 1.66/1.16  %Background operators:
% 1.66/1.16  
% 1.66/1.16  
% 1.66/1.16  %Foreground operators:
% 1.66/1.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.66/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.16  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.66/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.66/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.66/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.66/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.16  
% 1.66/1.17  tff(f_48, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r1_tarski(A, B) => ((k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A)) & (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_funct_1)).
% 1.66/1.17  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_relat_1)).
% 1.66/1.17  tff(f_31, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_relat_1)).
% 1.66/1.17  tff(c_12, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.66/1.17  tff(c_8, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.66/1.17  tff(c_4, plain, (![C_6, B_5, A_4]: (k7_relat_1(k7_relat_1(C_6, B_5), A_4)=k7_relat_1(C_6, A_4) | ~r1_tarski(A_4, B_5) | ~v1_relat_1(C_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.66/1.17  tff(c_2, plain, (![C_3, A_1, B_2]: (k7_relat_1(k7_relat_1(C_3, A_1), B_2)=k7_relat_1(C_3, A_1) | ~r1_tarski(A_1, B_2) | ~v1_relat_1(C_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.66/1.17  tff(c_6, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_2'), '#skF_1')!=k7_relat_1('#skF_3', '#skF_1') | k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')!=k7_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.66/1.17  tff(c_56, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')!=k7_relat_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_6])).
% 1.66/1.17  tff(c_62, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2, c_56])).
% 1.66/1.17  tff(c_68, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_8, c_62])).
% 1.66/1.17  tff(c_69, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_2'), '#skF_1')!=k7_relat_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_6])).
% 1.66/1.17  tff(c_73, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4, c_69])).
% 1.66/1.17  tff(c_80, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_8, c_73])).
% 1.66/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.17  
% 1.66/1.17  Inference rules
% 1.66/1.17  ----------------------
% 1.66/1.17  #Ref     : 0
% 1.66/1.17  #Sup     : 16
% 1.66/1.17  #Fact    : 0
% 1.66/1.17  #Define  : 0
% 1.66/1.17  #Split   : 1
% 1.66/1.17  #Chain   : 0
% 1.66/1.17  #Close   : 0
% 1.66/1.17  
% 1.66/1.17  Ordering : KBO
% 1.66/1.17  
% 1.66/1.17  Simplification rules
% 1.66/1.17  ----------------------
% 1.66/1.17  #Subsume      : 0
% 1.66/1.17  #Demod        : 5
% 1.66/1.17  #Tautology    : 5
% 1.66/1.17  #SimpNegUnit  : 0
% 1.66/1.17  #BackRed      : 0
% 1.66/1.17  
% 1.66/1.17  #Partial instantiations: 0
% 1.66/1.17  #Strategies tried      : 1
% 1.66/1.17  
% 1.66/1.17  Timing (in seconds)
% 1.66/1.17  ----------------------
% 1.66/1.17  Preprocessing        : 0.28
% 1.66/1.17  Parsing              : 0.16
% 1.66/1.17  CNF conversion       : 0.02
% 1.66/1.17  Main loop            : 0.11
% 1.66/1.17  Inferencing          : 0.05
% 1.66/1.17  Reduction            : 0.02
% 1.66/1.17  Demodulation         : 0.02
% 1.66/1.17  BG Simplification    : 0.01
% 1.66/1.17  Subsumption          : 0.01
% 1.66/1.17  Abstraction          : 0.01
% 1.66/1.17  MUC search           : 0.00
% 1.66/1.17  Cooper               : 0.00
% 1.66/1.17  Total                : 0.41
% 1.66/1.17  Index Insertion      : 0.00
% 1.66/1.17  Index Deletion       : 0.00
% 1.85/1.17  Index Matching       : 0.00
% 1.85/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
