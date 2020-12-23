%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:13 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   32 (  34 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  41 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_5 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_58,negated_conjecture,(
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

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_75,plain,(
    ! [D_83,A_84,B_85] :
      ( r2_hidden(k4_tarski(D_83,'#skF_5'(A_84,B_85,k10_relat_1(A_84,B_85),D_83)),A_84)
      | ~ r2_hidden(D_83,k10_relat_1(A_84,B_85))
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_28,plain,(
    ! [A_48,C_50,B_49] :
      ( r2_hidden(A_48,k1_relat_1(C_50))
      | ~ r2_hidden(k4_tarski(A_48,B_49),C_50)
      | ~ v1_relat_1(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_90,plain,(
    ! [D_86,A_87,B_88] :
      ( r2_hidden(D_86,k1_relat_1(A_87))
      | ~ r2_hidden(D_86,k10_relat_1(A_87,B_88))
      | ~ v1_relat_1(A_87) ) ),
    inference(resolution,[status(thm)],[c_75,c_28])).

tff(c_134,plain,(
    ! [A_92,B_93,B_94] :
      ( r2_hidden('#skF_1'(k10_relat_1(A_92,B_93),B_94),k1_relat_1(A_92))
      | ~ v1_relat_1(A_92)
      | r1_tarski(k10_relat_1(A_92,B_93),B_94) ) ),
    inference(resolution,[status(thm)],[c_6,c_90])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_146,plain,(
    ! [A_95,B_96] :
      ( ~ v1_relat_1(A_95)
      | r1_tarski(k10_relat_1(A_95,B_96),k1_relat_1(A_95)) ) ),
    inference(resolution,[status(thm)],[c_134,c_4])).

tff(c_30,plain,(
    ~ r1_tarski(k10_relat_1('#skF_7','#skF_6'),k1_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_151,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_146,c_30])).

tff(c_156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_151])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:53:15 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.27  
% 2.10/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.28  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_5 > #skF_3 > #skF_1
% 2.10/1.28  
% 2.10/1.28  %Foreground sorts:
% 2.10/1.28  
% 2.10/1.28  
% 2.10/1.28  %Background operators:
% 2.10/1.28  
% 2.10/1.28  
% 2.10/1.28  %Foreground operators:
% 2.10/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.28  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.10/1.28  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.10/1.28  tff('#skF_7', type, '#skF_7': $i).
% 2.10/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.10/1.28  tff('#skF_6', type, '#skF_6': $i).
% 2.10/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.10/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.28  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.10/1.28  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.10/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.10/1.28  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.10/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.10/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.10/1.28  
% 2.10/1.28  tff(f_58, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 2.10/1.28  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.10/1.28  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 2.10/1.28  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 2.10/1.28  tff(c_32, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.10/1.28  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.10/1.28  tff(c_75, plain, (![D_83, A_84, B_85]: (r2_hidden(k4_tarski(D_83, '#skF_5'(A_84, B_85, k10_relat_1(A_84, B_85), D_83)), A_84) | ~r2_hidden(D_83, k10_relat_1(A_84, B_85)) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.10/1.28  tff(c_28, plain, (![A_48, C_50, B_49]: (r2_hidden(A_48, k1_relat_1(C_50)) | ~r2_hidden(k4_tarski(A_48, B_49), C_50) | ~v1_relat_1(C_50))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.10/1.28  tff(c_90, plain, (![D_86, A_87, B_88]: (r2_hidden(D_86, k1_relat_1(A_87)) | ~r2_hidden(D_86, k10_relat_1(A_87, B_88)) | ~v1_relat_1(A_87))), inference(resolution, [status(thm)], [c_75, c_28])).
% 2.10/1.28  tff(c_134, plain, (![A_92, B_93, B_94]: (r2_hidden('#skF_1'(k10_relat_1(A_92, B_93), B_94), k1_relat_1(A_92)) | ~v1_relat_1(A_92) | r1_tarski(k10_relat_1(A_92, B_93), B_94))), inference(resolution, [status(thm)], [c_6, c_90])).
% 2.10/1.28  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.10/1.28  tff(c_146, plain, (![A_95, B_96]: (~v1_relat_1(A_95) | r1_tarski(k10_relat_1(A_95, B_96), k1_relat_1(A_95)))), inference(resolution, [status(thm)], [c_134, c_4])).
% 2.10/1.28  tff(c_30, plain, (~r1_tarski(k10_relat_1('#skF_7', '#skF_6'), k1_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.10/1.28  tff(c_151, plain, (~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_146, c_30])).
% 2.10/1.28  tff(c_156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_151])).
% 2.10/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.28  
% 2.10/1.28  Inference rules
% 2.10/1.28  ----------------------
% 2.10/1.28  #Ref     : 0
% 2.10/1.28  #Sup     : 28
% 2.10/1.28  #Fact    : 0
% 2.10/1.28  #Define  : 0
% 2.10/1.28  #Split   : 0
% 2.10/1.28  #Chain   : 0
% 2.10/1.28  #Close   : 0
% 2.10/1.28  
% 2.10/1.28  Ordering : KBO
% 2.10/1.28  
% 2.10/1.28  Simplification rules
% 2.10/1.28  ----------------------
% 2.10/1.28  #Subsume      : 1
% 2.10/1.28  #Demod        : 1
% 2.10/1.28  #Tautology    : 1
% 2.10/1.28  #SimpNegUnit  : 0
% 2.10/1.28  #BackRed      : 0
% 2.10/1.28  
% 2.10/1.28  #Partial instantiations: 0
% 2.10/1.28  #Strategies tried      : 1
% 2.10/1.28  
% 2.10/1.28  Timing (in seconds)
% 2.10/1.28  ----------------------
% 2.10/1.29  Preprocessing        : 0.30
% 2.10/1.29  Parsing              : 0.16
% 2.10/1.29  CNF conversion       : 0.03
% 2.10/1.29  Main loop            : 0.18
% 2.10/1.29  Inferencing          : 0.07
% 2.10/1.29  Reduction            : 0.04
% 2.10/1.29  Demodulation         : 0.03
% 2.10/1.29  BG Simplification    : 0.02
% 2.10/1.29  Subsumption          : 0.04
% 2.10/1.29  Abstraction          : 0.01
% 2.10/1.29  MUC search           : 0.00
% 2.10/1.29  Cooper               : 0.00
% 2.10/1.29  Total                : 0.50
% 2.10/1.29  Index Insertion      : 0.00
% 2.10/1.29  Index Deletion       : 0.00
% 2.10/1.29  Index Matching       : 0.00
% 2.10/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
