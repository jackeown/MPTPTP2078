%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:59 EST 2020

% Result     : Theorem 1.57s
% Output     : CNFRefutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   25 (  29 expanded)
%              Number of leaves         :   13 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :   40 (  60 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( v1_relat_1(C)
           => ( ( r1_tarski(k1_relat_1(C),A)
                & r1_tarski(C,B) )
             => r1_tarski(C,k7_relat_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ! [D] :
          ( v1_relat_1(D)
         => ( ( r1_tarski(C,D)
              & r1_tarski(A,B) )
           => r1_tarski(k7_relat_1(C,A),k7_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_relat_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [A_6] :
      ( k7_relat_1(A_6,k1_relat_1(A_6)) = A_6
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_24,plain,(
    ! [C_9,A_10,D_11,B_12] :
      ( r1_tarski(k7_relat_1(C_9,A_10),k7_relat_1(D_11,B_12))
      | ~ r1_tarski(A_10,B_12)
      | ~ r1_tarski(C_9,D_11)
      | ~ v1_relat_1(D_11)
      | ~ v1_relat_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_31,plain,(
    ! [A_13,D_14,B_15] :
      ( r1_tarski(A_13,k7_relat_1(D_14,B_15))
      | ~ r1_tarski(k1_relat_1(A_13),B_15)
      | ~ r1_tarski(A_13,D_14)
      | ~ v1_relat_1(D_14)
      | ~ v1_relat_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_24])).

tff(c_33,plain,(
    ! [D_14] :
      ( r1_tarski('#skF_3',k7_relat_1(D_14,'#skF_1'))
      | ~ r1_tarski('#skF_3',D_14)
      | ~ v1_relat_1(D_14)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_10,c_31])).

tff(c_37,plain,(
    ! [D_16] :
      ( r1_tarski('#skF_3',k7_relat_1(D_16,'#skF_1'))
      | ~ r1_tarski('#skF_3',D_16)
      | ~ v1_relat_1(D_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_33])).

tff(c_6,plain,(
    ~ r1_tarski('#skF_3',k7_relat_1('#skF_2','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_40,plain,
    ( ~ r1_tarski('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_37,c_6])).

tff(c_44,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_8,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:43:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.57/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.57/1.14  
% 1.57/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.57/1.15  %$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.57/1.15  
% 1.57/1.15  %Foreground sorts:
% 1.57/1.15  
% 1.57/1.15  
% 1.57/1.15  %Background operators:
% 1.57/1.15  
% 1.57/1.15  
% 1.57/1.15  %Foreground operators:
% 1.57/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.57/1.15  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.57/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.57/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.57/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.57/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.57/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.57/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.57/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.57/1.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.57/1.15  
% 1.57/1.16  tff(f_52, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(C, B)) => r1_tarski(C, k7_relat_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t186_relat_1)).
% 1.57/1.16  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 1.57/1.16  tff(f_36, axiom, (![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k7_relat_1(C, A), k7_relat_1(D, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_relat_1)).
% 1.57/1.16  tff(c_14, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.57/1.16  tff(c_8, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.57/1.16  tff(c_12, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.57/1.16  tff(c_10, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.57/1.16  tff(c_4, plain, (![A_6]: (k7_relat_1(A_6, k1_relat_1(A_6))=A_6 | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.57/1.16  tff(c_24, plain, (![C_9, A_10, D_11, B_12]: (r1_tarski(k7_relat_1(C_9, A_10), k7_relat_1(D_11, B_12)) | ~r1_tarski(A_10, B_12) | ~r1_tarski(C_9, D_11) | ~v1_relat_1(D_11) | ~v1_relat_1(C_9))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.57/1.16  tff(c_31, plain, (![A_13, D_14, B_15]: (r1_tarski(A_13, k7_relat_1(D_14, B_15)) | ~r1_tarski(k1_relat_1(A_13), B_15) | ~r1_tarski(A_13, D_14) | ~v1_relat_1(D_14) | ~v1_relat_1(A_13) | ~v1_relat_1(A_13))), inference(superposition, [status(thm), theory('equality')], [c_4, c_24])).
% 1.57/1.16  tff(c_33, plain, (![D_14]: (r1_tarski('#skF_3', k7_relat_1(D_14, '#skF_1')) | ~r1_tarski('#skF_3', D_14) | ~v1_relat_1(D_14) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_10, c_31])).
% 1.57/1.16  tff(c_37, plain, (![D_16]: (r1_tarski('#skF_3', k7_relat_1(D_16, '#skF_1')) | ~r1_tarski('#skF_3', D_16) | ~v1_relat_1(D_16))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_33])).
% 1.57/1.16  tff(c_6, plain, (~r1_tarski('#skF_3', k7_relat_1('#skF_2', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.57/1.16  tff(c_40, plain, (~r1_tarski('#skF_3', '#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_37, c_6])).
% 1.57/1.16  tff(c_44, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_8, c_40])).
% 1.57/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.57/1.16  
% 1.57/1.16  Inference rules
% 1.57/1.16  ----------------------
% 1.57/1.16  #Ref     : 0
% 1.57/1.16  #Sup     : 6
% 1.57/1.16  #Fact    : 0
% 1.57/1.16  #Define  : 0
% 1.57/1.16  #Split   : 0
% 1.57/1.16  #Chain   : 0
% 1.57/1.16  #Close   : 0
% 1.57/1.16  
% 1.57/1.16  Ordering : KBO
% 1.57/1.16  
% 1.57/1.16  Simplification rules
% 1.57/1.16  ----------------------
% 1.57/1.16  #Subsume      : 0
% 1.57/1.16  #Demod        : 3
% 1.57/1.16  #Tautology    : 2
% 1.57/1.16  #SimpNegUnit  : 0
% 1.57/1.16  #BackRed      : 0
% 1.57/1.16  
% 1.57/1.16  #Partial instantiations: 0
% 1.57/1.16  #Strategies tried      : 1
% 1.57/1.16  
% 1.57/1.16  Timing (in seconds)
% 1.57/1.16  ----------------------
% 1.57/1.16  Preprocessing        : 0.25
% 1.57/1.16  Parsing              : 0.14
% 1.57/1.16  CNF conversion       : 0.02
% 1.57/1.16  Main loop            : 0.08
% 1.57/1.16  Inferencing          : 0.04
% 1.57/1.16  Reduction            : 0.02
% 1.57/1.16  Demodulation         : 0.02
% 1.57/1.16  BG Simplification    : 0.01
% 1.57/1.16  Subsumption          : 0.01
% 1.57/1.16  Abstraction          : 0.00
% 1.57/1.16  MUC search           : 0.00
% 1.57/1.16  Cooper               : 0.00
% 1.57/1.16  Total                : 0.36
% 1.57/1.16  Index Insertion      : 0.00
% 1.57/1.16  Index Deletion       : 0.00
% 1.57/1.16  Index Matching       : 0.00
% 1.57/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
