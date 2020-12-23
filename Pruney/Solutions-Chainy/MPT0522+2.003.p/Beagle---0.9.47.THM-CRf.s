%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:10 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
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
           => r1_tarski(k5_relat_1(B,k8_relat_1(A,C)),k5_relat_1(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t122_relat_1)).

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

tff(c_16,plain,(
    v1_relat_1('#skF_3') ),
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

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
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
    ~ r1_tarski(k5_relat_1('#skF_2',k8_relat_1('#skF_1','#skF_3')),k5_relat_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_37,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_14])).

tff(c_42,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_6,c_37])).

tff(c_44,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_47,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_44])).

tff(c_51,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_47])).

tff(c_52,plain,(
    ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_56,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_52])).

tff(c_60,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:11:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.11  
% 1.63/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.11  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k5_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.63/1.11  
% 1.63/1.11  %Foreground sorts:
% 1.63/1.11  
% 1.63/1.11  
% 1.63/1.11  %Background operators:
% 1.63/1.11  
% 1.63/1.11  
% 1.63/1.11  %Foreground operators:
% 1.63/1.11  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.63/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.11  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.63/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.63/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.63/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.63/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.11  
% 1.63/1.12  tff(f_64, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(B, k8_relat_1(A, C)), k5_relat_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t122_relat_1)).
% 1.63/1.12  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 1.63/1.12  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 1.63/1.12  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.63/1.12  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k5_relat_1(A, C), k5_relat_1(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relat_1)).
% 1.63/1.12  tff(c_16, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.63/1.12  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k8_relat_1(A_5, B_6), B_6) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.63/1.12  tff(c_8, plain, (![A_3, B_4]: (v1_relat_1(k8_relat_1(A_3, B_4)) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.63/1.12  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.63/1.12  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.63/1.12  tff(c_34, plain, (![A_32, C_33, B_34, D_35]: (r1_tarski(k5_relat_1(A_32, C_33), k5_relat_1(B_34, D_35)) | ~r1_tarski(C_33, D_35) | ~r1_tarski(A_32, B_34) | ~v1_relat_1(D_35) | ~v1_relat_1(C_33) | ~v1_relat_1(B_34) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.63/1.12  tff(c_14, plain, (~r1_tarski(k5_relat_1('#skF_2', k8_relat_1('#skF_1', '#skF_3')), k5_relat_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.63/1.12  tff(c_37, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), '#skF_3') | ~r1_tarski('#skF_2', '#skF_2') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_3')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_34, c_14])).
% 1.63/1.12  tff(c_42, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), '#skF_3') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_6, c_37])).
% 1.63/1.12  tff(c_44, plain, (~v1_relat_1(k8_relat_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_42])).
% 1.63/1.12  tff(c_47, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_44])).
% 1.63/1.12  tff(c_51, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_47])).
% 1.63/1.12  tff(c_52, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_42])).
% 1.63/1.12  tff(c_56, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_52])).
% 1.63/1.12  tff(c_60, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_56])).
% 1.63/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.12  
% 1.63/1.12  Inference rules
% 1.63/1.12  ----------------------
% 1.63/1.12  #Ref     : 0
% 1.63/1.12  #Sup     : 6
% 1.63/1.12  #Fact    : 0
% 1.63/1.12  #Define  : 0
% 1.63/1.12  #Split   : 1
% 1.63/1.12  #Chain   : 0
% 1.63/1.12  #Close   : 0
% 1.63/1.12  
% 1.63/1.12  Ordering : KBO
% 1.63/1.12  
% 1.63/1.12  Simplification rules
% 1.63/1.12  ----------------------
% 1.63/1.12  #Subsume      : 0
% 1.63/1.12  #Demod        : 7
% 1.63/1.12  #Tautology    : 2
% 1.63/1.12  #SimpNegUnit  : 0
% 1.63/1.12  #BackRed      : 0
% 1.63/1.12  
% 1.63/1.12  #Partial instantiations: 0
% 1.63/1.12  #Strategies tried      : 1
% 1.63/1.12  
% 1.63/1.12  Timing (in seconds)
% 1.63/1.12  ----------------------
% 1.63/1.12  Preprocessing        : 0.26
% 1.63/1.12  Parsing              : 0.15
% 1.63/1.12  CNF conversion       : 0.02
% 1.63/1.12  Main loop            : 0.10
% 1.63/1.12  Inferencing          : 0.04
% 1.63/1.12  Reduction            : 0.02
% 1.63/1.12  Demodulation         : 0.02
% 1.63/1.12  BG Simplification    : 0.01
% 1.63/1.12  Subsumption          : 0.02
% 1.63/1.12  Abstraction          : 0.00
% 1.63/1.12  MUC search           : 0.00
% 1.63/1.12  Cooper               : 0.00
% 1.63/1.12  Total                : 0.39
% 1.63/1.12  Index Insertion      : 0.00
% 1.63/1.12  Index Deletion       : 0.00
% 1.63/1.12  Index Matching       : 0.00
% 1.63/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
