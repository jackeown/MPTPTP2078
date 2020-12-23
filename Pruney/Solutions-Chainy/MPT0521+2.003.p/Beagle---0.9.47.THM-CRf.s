%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:09 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   30 (  48 expanded)
%              Number of leaves         :   15 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 (  96 expanded)
%              Number of equality atoms :    1 (   2 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > k5_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( v1_relat_1(C)
           => r1_tarski(k5_relat_1(k8_relat_1(A,B),C),k5_relat_1(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_relat_1)).

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

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ! [D] :
                  ( v1_relat_1(D)
                 => ( ( r1_tarski(A,B)
                      & r1_tarski(C,D) )
                   => r1_tarski(k5_relat_1(A,C),k5_relat_1(B,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relat_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

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

tff(c_16,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    ! [A_32,C_33,B_34,D_35] :
      ( r1_tarski(k5_relat_1(A_32,C_33),k5_relat_1(B_34,D_35))
      | ~ r1_tarski(C_33,D_35)
      | ~ r1_tarski(A_32,B_34)
      | ~ v1_relat_1(D_35)
      | ~ v1_relat_1(C_33)
      | ~ v1_relat_1(B_34)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    ~ r1_tarski(k5_relat_1(k8_relat_1('#skF_1','#skF_2'),'#skF_3'),k5_relat_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_37,plain,
    ( ~ r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski(k8_relat_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_14])).

tff(c_42,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_6,c_37])).

tff(c_44,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_47,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_44])).

tff(c_51,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_47])).

tff(c_52,plain,(
    ~ r1_tarski(k8_relat_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_56,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_52])).

tff(c_60,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:00:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.18  
% 1.74/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.18  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k5_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.74/1.18  
% 1.74/1.18  %Foreground sorts:
% 1.74/1.18  
% 1.74/1.18  
% 1.74/1.18  %Background operators:
% 1.74/1.18  
% 1.74/1.18  
% 1.74/1.18  %Foreground operators:
% 1.74/1.18  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.74/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.74/1.18  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.74/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.74/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.74/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.74/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.74/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.74/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.74/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.74/1.18  
% 1.74/1.19  tff(f_64, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(k8_relat_1(A, B), C), k5_relat_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_relat_1)).
% 1.74/1.19  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 1.74/1.19  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 1.74/1.19  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.74/1.19  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k5_relat_1(A, C), k5_relat_1(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relat_1)).
% 1.74/1.19  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.74/1.19  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k8_relat_1(A_5, B_6), B_6) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.74/1.19  tff(c_8, plain, (![A_3, B_4]: (v1_relat_1(k8_relat_1(A_3, B_4)) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.74/1.19  tff(c_16, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.74/1.19  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.74/1.19  tff(c_34, plain, (![A_32, C_33, B_34, D_35]: (r1_tarski(k5_relat_1(A_32, C_33), k5_relat_1(B_34, D_35)) | ~r1_tarski(C_33, D_35) | ~r1_tarski(A_32, B_34) | ~v1_relat_1(D_35) | ~v1_relat_1(C_33) | ~v1_relat_1(B_34) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.74/1.19  tff(c_14, plain, (~r1_tarski(k5_relat_1(k8_relat_1('#skF_1', '#skF_2'), '#skF_3'), k5_relat_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.74/1.19  tff(c_37, plain, (~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski(k8_relat_1('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_14])).
% 1.74/1.19  tff(c_42, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_6, c_37])).
% 1.74/1.19  tff(c_44, plain, (~v1_relat_1(k8_relat_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_42])).
% 1.74/1.19  tff(c_47, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_44])).
% 1.74/1.19  tff(c_51, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_47])).
% 1.74/1.19  tff(c_52, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_42])).
% 1.74/1.19  tff(c_56, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10, c_52])).
% 1.74/1.19  tff(c_60, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_56])).
% 1.74/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.19  
% 1.74/1.19  Inference rules
% 1.74/1.19  ----------------------
% 1.74/1.19  #Ref     : 0
% 1.74/1.19  #Sup     : 6
% 1.74/1.19  #Fact    : 0
% 1.74/1.19  #Define  : 0
% 1.74/1.19  #Split   : 1
% 1.74/1.19  #Chain   : 0
% 1.74/1.19  #Close   : 0
% 1.74/1.19  
% 1.74/1.19  Ordering : KBO
% 1.74/1.19  
% 1.74/1.19  Simplification rules
% 1.74/1.19  ----------------------
% 1.74/1.19  #Subsume      : 0
% 1.74/1.19  #Demod        : 7
% 1.74/1.19  #Tautology    : 2
% 1.74/1.19  #SimpNegUnit  : 0
% 1.74/1.19  #BackRed      : 0
% 1.74/1.19  
% 1.74/1.19  #Partial instantiations: 0
% 1.74/1.19  #Strategies tried      : 1
% 1.74/1.19  
% 1.74/1.19  Timing (in seconds)
% 1.74/1.19  ----------------------
% 1.74/1.19  Preprocessing        : 0.27
% 1.74/1.19  Parsing              : 0.16
% 1.74/1.19  CNF conversion       : 0.02
% 1.74/1.20  Main loop            : 0.10
% 1.74/1.20  Inferencing          : 0.04
% 1.74/1.20  Reduction            : 0.02
% 1.74/1.20  Demodulation         : 0.02
% 1.74/1.20  BG Simplification    : 0.01
% 1.74/1.20  Subsumption          : 0.02
% 1.74/1.20  Abstraction          : 0.00
% 1.74/1.20  MUC search           : 0.00
% 1.74/1.20  Cooper               : 0.00
% 1.74/1.20  Total                : 0.39
% 1.74/1.20  Index Insertion      : 0.00
% 1.74/1.20  Index Deletion       : 0.00
% 1.74/1.20  Index Matching       : 0.00
% 1.74/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
