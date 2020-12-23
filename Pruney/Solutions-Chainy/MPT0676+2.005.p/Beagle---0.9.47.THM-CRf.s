%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:24 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   34 (  53 expanded)
%              Number of leaves         :   18 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   43 (  92 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k8_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => r1_tarski(k9_relat_1(k8_relat_1(A,C),B),k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_funct_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ! [D] :
          ( v1_relat_1(D)
         => ( ( r1_tarski(C,D)
              & r1_tarski(A,B) )
           => r1_tarski(k9_relat_1(C,A),k9_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(k8_relat_1(A_8,B_9),B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k8_relat_1(A_6,B_7))
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_22,plain,(
    ! [A_21,B_22] :
      ( r2_hidden('#skF_1'(A_21,B_22),A_21)
      | r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_27,plain,(
    ! [A_21] : r1_tarski(A_21,A_21) ),
    inference(resolution,[status(thm)],[c_22,c_4])).

tff(c_33,plain,(
    ! [C_27,A_28,D_29,B_30] :
      ( r1_tarski(k9_relat_1(C_27,A_28),k9_relat_1(D_29,B_30))
      | ~ r1_tarski(A_28,B_30)
      | ~ r1_tarski(C_27,D_29)
      | ~ v1_relat_1(D_29)
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    ~ r1_tarski(k9_relat_1(k8_relat_1('#skF_2','#skF_4'),'#skF_3'),k9_relat_1('#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_36,plain,
    ( ~ r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski(k8_relat_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k8_relat_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_33,c_14])).

tff(c_39,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v1_relat_1(k8_relat_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_27,c_36])).

tff(c_40,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_39])).

tff(c_43,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_40])).

tff(c_47,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_43])).

tff(c_48,plain,(
    ~ r1_tarski(k8_relat_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_39])).

tff(c_52,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_48])).

tff(c_56,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:55:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.42  
% 2.03/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.44  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k8_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.03/1.44  
% 2.03/1.44  %Foreground sorts:
% 2.03/1.44  
% 2.03/1.44  
% 2.03/1.44  %Background operators:
% 2.03/1.44  
% 2.03/1.44  
% 2.03/1.44  %Foreground operators:
% 2.03/1.44  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.03/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.03/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.03/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.03/1.44  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.03/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.03/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.03/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.03/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.03/1.44  
% 2.12/1.45  tff(f_58, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => r1_tarski(k9_relat_1(k8_relat_1(A, C), B), k9_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_funct_1)).
% 2.12/1.45  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 2.12/1.45  tff(f_36, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 2.12/1.45  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.12/1.45  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k9_relat_1(C, A), k9_relat_1(D, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_relat_1)).
% 2.12/1.45  tff(c_18, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.12/1.45  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(k8_relat_1(A_8, B_9), B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.12/1.45  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k8_relat_1(A_6, B_7)) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.12/1.45  tff(c_22, plain, (![A_21, B_22]: (r2_hidden('#skF_1'(A_21, B_22), A_21) | r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.12/1.45  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.12/1.45  tff(c_27, plain, (![A_21]: (r1_tarski(A_21, A_21))), inference(resolution, [status(thm)], [c_22, c_4])).
% 2.12/1.45  tff(c_33, plain, (![C_27, A_28, D_29, B_30]: (r1_tarski(k9_relat_1(C_27, A_28), k9_relat_1(D_29, B_30)) | ~r1_tarski(A_28, B_30) | ~r1_tarski(C_27, D_29) | ~v1_relat_1(D_29) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.12/1.45  tff(c_14, plain, (~r1_tarski(k9_relat_1(k8_relat_1('#skF_2', '#skF_4'), '#skF_3'), k9_relat_1('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.12/1.45  tff(c_36, plain, (~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski(k8_relat_1('#skF_2', '#skF_4'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k8_relat_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_33, c_14])).
% 2.12/1.45  tff(c_39, plain, (~r1_tarski(k8_relat_1('#skF_2', '#skF_4'), '#skF_4') | ~v1_relat_1(k8_relat_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_27, c_36])).
% 2.12/1.45  tff(c_40, plain, (~v1_relat_1(k8_relat_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_39])).
% 2.12/1.45  tff(c_43, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8, c_40])).
% 2.12/1.45  tff(c_47, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_43])).
% 2.12/1.45  tff(c_48, plain, (~r1_tarski(k8_relat_1('#skF_2', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_39])).
% 2.12/1.45  tff(c_52, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_48])).
% 2.12/1.45  tff(c_56, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_52])).
% 2.12/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.45  
% 2.12/1.45  Inference rules
% 2.12/1.45  ----------------------
% 2.12/1.45  #Ref     : 0
% 2.12/1.45  #Sup     : 5
% 2.12/1.45  #Fact    : 0
% 2.12/1.45  #Define  : 0
% 2.12/1.45  #Split   : 1
% 2.12/1.45  #Chain   : 0
% 2.12/1.45  #Close   : 0
% 2.12/1.45  
% 2.12/1.45  Ordering : KBO
% 2.12/1.45  
% 2.12/1.45  Simplification rules
% 2.12/1.45  ----------------------
% 2.12/1.45  #Subsume      : 0
% 2.12/1.45  #Demod        : 4
% 2.12/1.45  #Tautology    : 0
% 2.12/1.45  #SimpNegUnit  : 0
% 2.12/1.45  #BackRed      : 0
% 2.12/1.45  
% 2.12/1.45  #Partial instantiations: 0
% 2.12/1.45  #Strategies tried      : 1
% 2.12/1.45  
% 2.12/1.45  Timing (in seconds)
% 2.12/1.45  ----------------------
% 2.15/1.46  Preprocessing        : 0.42
% 2.15/1.46  Parsing              : 0.23
% 2.15/1.46  CNF conversion       : 0.03
% 2.15/1.46  Main loop            : 0.18
% 2.15/1.46  Inferencing          : 0.07
% 2.15/1.46  Reduction            : 0.04
% 2.15/1.46  Demodulation         : 0.04
% 2.15/1.46  BG Simplification    : 0.01
% 2.15/1.46  Subsumption          : 0.03
% 2.15/1.46  Abstraction          : 0.01
% 2.15/1.46  MUC search           : 0.00
% 2.15/1.46  Cooper               : 0.00
% 2.15/1.46  Total                : 0.65
% 2.15/1.46  Index Insertion      : 0.00
% 2.15/1.46  Index Deletion       : 0.00
% 2.15/1.46  Index Matching       : 0.00
% 2.15/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
