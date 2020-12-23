%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:38 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   28 (  44 expanded)
%              Number of leaves         :   14 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  78 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(f_53,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( v1_relat_1(C)
           => r1_tarski(k5_relat_1(k7_relat_1(B,A),C),k5_relat_1(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(A,C),k5_relat_1(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relat_1)).

tff(c_12,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k7_relat_1(B_11,A_10),B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k7_relat_1(A_1,B_2))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_15,plain,(
    ! [A_17,C_18,B_19] :
      ( r1_tarski(k5_relat_1(A_17,C_18),k5_relat_1(B_19,C_18))
      | ~ r1_tarski(A_17,B_19)
      | ~ v1_relat_1(C_18)
      | ~ v1_relat_1(B_19)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ~ r1_tarski(k5_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_3'),k5_relat_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_15,c_8])).

tff(c_21,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10,c_18])).

tff(c_22,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_21])).

tff(c_25,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_22])).

tff(c_29,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_25])).

tff(c_30,plain,(
    ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_21])).

tff(c_34,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_30])).

tff(c_38,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:44:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.16  
% 1.70/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.17  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.70/1.17  
% 1.70/1.17  %Foreground sorts:
% 1.70/1.17  
% 1.70/1.17  
% 1.70/1.17  %Background operators:
% 1.70/1.17  
% 1.70/1.17  
% 1.70/1.17  %Foreground operators:
% 1.70/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.17  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.70/1.17  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.70/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.70/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.70/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.70/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.70/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.70/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.17  
% 1.70/1.17  tff(f_53, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(k7_relat_1(B, A), C), k5_relat_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_relat_1)).
% 1.70/1.17  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 1.70/1.17  tff(f_29, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.70/1.17  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(A, C), k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relat_1)).
% 1.70/1.17  tff(c_12, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.70/1.17  tff(c_6, plain, (![B_11, A_10]: (r1_tarski(k7_relat_1(B_11, A_10), B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.70/1.17  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k7_relat_1(A_1, B_2)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.70/1.17  tff(c_10, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.70/1.17  tff(c_15, plain, (![A_17, C_18, B_19]: (r1_tarski(k5_relat_1(A_17, C_18), k5_relat_1(B_19, C_18)) | ~r1_tarski(A_17, B_19) | ~v1_relat_1(C_18) | ~v1_relat_1(B_19) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.70/1.17  tff(c_8, plain, (~r1_tarski(k5_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_3'), k5_relat_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.70/1.17  tff(c_18, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_15, c_8])).
% 1.70/1.17  tff(c_21, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_10, c_18])).
% 1.70/1.17  tff(c_22, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_21])).
% 1.70/1.17  tff(c_25, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2, c_22])).
% 1.70/1.17  tff(c_29, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_25])).
% 1.70/1.17  tff(c_30, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_21])).
% 1.70/1.17  tff(c_34, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_6, c_30])).
% 1.70/1.17  tff(c_38, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_34])).
% 1.70/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.17  
% 1.70/1.17  Inference rules
% 1.70/1.17  ----------------------
% 1.70/1.17  #Ref     : 0
% 1.70/1.18  #Sup     : 3
% 1.70/1.18  #Fact    : 0
% 1.70/1.18  #Define  : 0
% 1.70/1.18  #Split   : 1
% 1.70/1.18  #Chain   : 0
% 1.70/1.18  #Close   : 0
% 1.70/1.18  
% 1.70/1.18  Ordering : KBO
% 1.70/1.18  
% 1.70/1.18  Simplification rules
% 1.70/1.18  ----------------------
% 1.70/1.18  #Subsume      : 0
% 1.70/1.18  #Demod        : 4
% 1.70/1.18  #Tautology    : 0
% 1.70/1.18  #SimpNegUnit  : 0
% 1.70/1.18  #BackRed      : 0
% 1.70/1.18  
% 1.70/1.18  #Partial instantiations: 0
% 1.70/1.18  #Strategies tried      : 1
% 1.70/1.18  
% 1.70/1.18  Timing (in seconds)
% 1.70/1.18  ----------------------
% 1.70/1.18  Preprocessing        : 0.28
% 1.70/1.18  Parsing              : 0.15
% 1.70/1.18  CNF conversion       : 0.02
% 1.70/1.18  Main loop            : 0.08
% 1.70/1.18  Inferencing          : 0.03
% 1.70/1.18  Reduction            : 0.02
% 1.70/1.18  Demodulation         : 0.02
% 1.70/1.18  BG Simplification    : 0.01
% 1.70/1.18  Subsumption          : 0.01
% 1.70/1.18  Abstraction          : 0.00
% 1.70/1.18  MUC search           : 0.00
% 1.70/1.18  Cooper               : 0.00
% 1.70/1.18  Total                : 0.39
% 1.70/1.18  Index Insertion      : 0.00
% 1.70/1.18  Index Deletion       : 0.00
% 1.70/1.18  Index Matching       : 0.00
% 1.70/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
