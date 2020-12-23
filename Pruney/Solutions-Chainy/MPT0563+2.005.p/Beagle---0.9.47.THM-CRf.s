%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:14 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   29 (  31 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  41 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,(
    ! [A_42,B_43,C_44] :
      ( r2_hidden(k4_tarski(A_42,'#skF_2'(A_42,B_43,C_44)),C_44)
      | ~ r2_hidden(A_42,k10_relat_1(C_44,B_43))
      | ~ v1_relat_1(C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [A_12,C_14,B_13] :
      ( r2_hidden(A_12,k1_relat_1(C_14))
      | ~ r2_hidden(k4_tarski(A_12,B_13),C_14)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_70,plain,(
    ! [A_45,C_46,B_47] :
      ( r2_hidden(A_45,k1_relat_1(C_46))
      | ~ r2_hidden(A_45,k10_relat_1(C_46,B_47))
      | ~ v1_relat_1(C_46) ) ),
    inference(resolution,[status(thm)],[c_58,c_18])).

tff(c_91,plain,(
    ! [C_48,B_49,B_50] :
      ( r2_hidden('#skF_1'(k10_relat_1(C_48,B_49),B_50),k1_relat_1(C_48))
      | ~ v1_relat_1(C_48)
      | r1_tarski(k10_relat_1(C_48,B_49),B_50) ) ),
    inference(resolution,[status(thm)],[c_6,c_70])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_119,plain,(
    ! [C_55,B_56] :
      ( ~ v1_relat_1(C_55)
      | r1_tarski(k10_relat_1(C_55,B_56),k1_relat_1(C_55)) ) ),
    inference(resolution,[status(thm)],[c_91,c_4])).

tff(c_20,plain,(
    ~ r1_tarski(k10_relat_1('#skF_4','#skF_3'),k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_124,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_119,c_20])).

tff(c_129,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_124])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:18:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.21  
% 1.89/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.21  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 1.89/1.21  
% 1.89/1.21  %Foreground sorts:
% 1.89/1.21  
% 1.89/1.21  
% 1.89/1.21  %Background operators:
% 1.89/1.21  
% 1.89/1.21  
% 1.89/1.21  %Foreground operators:
% 1.89/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.89/1.21  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.89/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.89/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.89/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.89/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.21  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.89/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.89/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.89/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.89/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.89/1.21  
% 1.89/1.22  tff(f_56, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 1.89/1.22  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.89/1.22  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 1.89/1.22  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 1.89/1.22  tff(c_22, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.89/1.22  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.89/1.22  tff(c_58, plain, (![A_42, B_43, C_44]: (r2_hidden(k4_tarski(A_42, '#skF_2'(A_42, B_43, C_44)), C_44) | ~r2_hidden(A_42, k10_relat_1(C_44, B_43)) | ~v1_relat_1(C_44))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.89/1.22  tff(c_18, plain, (![A_12, C_14, B_13]: (r2_hidden(A_12, k1_relat_1(C_14)) | ~r2_hidden(k4_tarski(A_12, B_13), C_14) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.89/1.22  tff(c_70, plain, (![A_45, C_46, B_47]: (r2_hidden(A_45, k1_relat_1(C_46)) | ~r2_hidden(A_45, k10_relat_1(C_46, B_47)) | ~v1_relat_1(C_46))), inference(resolution, [status(thm)], [c_58, c_18])).
% 1.89/1.22  tff(c_91, plain, (![C_48, B_49, B_50]: (r2_hidden('#skF_1'(k10_relat_1(C_48, B_49), B_50), k1_relat_1(C_48)) | ~v1_relat_1(C_48) | r1_tarski(k10_relat_1(C_48, B_49), B_50))), inference(resolution, [status(thm)], [c_6, c_70])).
% 1.89/1.22  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.89/1.22  tff(c_119, plain, (![C_55, B_56]: (~v1_relat_1(C_55) | r1_tarski(k10_relat_1(C_55, B_56), k1_relat_1(C_55)))), inference(resolution, [status(thm)], [c_91, c_4])).
% 1.89/1.22  tff(c_20, plain, (~r1_tarski(k10_relat_1('#skF_4', '#skF_3'), k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.89/1.22  tff(c_124, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_119, c_20])).
% 1.89/1.22  tff(c_129, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_124])).
% 1.89/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.22  
% 1.89/1.22  Inference rules
% 1.89/1.22  ----------------------
% 1.89/1.22  #Ref     : 0
% 1.89/1.22  #Sup     : 24
% 1.89/1.22  #Fact    : 0
% 1.89/1.22  #Define  : 0
% 1.89/1.22  #Split   : 0
% 1.89/1.22  #Chain   : 0
% 1.89/1.22  #Close   : 0
% 1.89/1.22  
% 1.89/1.22  Ordering : KBO
% 1.89/1.22  
% 1.89/1.22  Simplification rules
% 1.89/1.22  ----------------------
% 1.89/1.22  #Subsume      : 2
% 1.89/1.22  #Demod        : 1
% 1.89/1.22  #Tautology    : 1
% 1.89/1.22  #SimpNegUnit  : 0
% 1.89/1.22  #BackRed      : 0
% 1.89/1.22  
% 1.89/1.22  #Partial instantiations: 0
% 1.89/1.22  #Strategies tried      : 1
% 1.89/1.22  
% 1.89/1.22  Timing (in seconds)
% 1.89/1.22  ----------------------
% 1.89/1.22  Preprocessing        : 0.29
% 1.89/1.22  Parsing              : 0.16
% 1.89/1.22  CNF conversion       : 0.02
% 1.89/1.23  Main loop            : 0.18
% 1.89/1.23  Inferencing          : 0.08
% 1.89/1.23  Reduction            : 0.04
% 1.89/1.23  Demodulation         : 0.03
% 1.89/1.23  BG Simplification    : 0.02
% 1.89/1.23  Subsumption          : 0.04
% 1.89/1.23  Abstraction          : 0.01
% 1.89/1.23  MUC search           : 0.00
% 1.89/1.23  Cooper               : 0.00
% 1.89/1.23  Total                : 0.49
% 1.89/1.23  Index Insertion      : 0.00
% 1.89/1.23  Index Deletion       : 0.00
% 1.89/1.23  Index Matching       : 0.00
% 1.89/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
