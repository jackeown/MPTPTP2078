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
% DateTime   : Thu Dec  3 10:00:32 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
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
%$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_5 > #skF_3 > #skF_1

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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
       => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(E,D),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_75,plain,(
    ! [A_83,B_84,D_85] :
      ( r2_hidden(k4_tarski('#skF_5'(A_83,B_84,k9_relat_1(A_83,B_84),D_85),D_85),A_83)
      | ~ r2_hidden(D_85,k9_relat_1(A_83,B_84))
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_26,plain,(
    ! [B_49,C_50,A_48] :
      ( r2_hidden(B_49,k2_relat_1(C_50))
      | ~ r2_hidden(k4_tarski(A_48,B_49),C_50)
      | ~ v1_relat_1(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_90,plain,(
    ! [D_86,A_87,B_88] :
      ( r2_hidden(D_86,k2_relat_1(A_87))
      | ~ r2_hidden(D_86,k9_relat_1(A_87,B_88))
      | ~ v1_relat_1(A_87) ) ),
    inference(resolution,[status(thm)],[c_75,c_26])).

tff(c_134,plain,(
    ! [A_92,B_93,B_94] :
      ( r2_hidden('#skF_1'(k9_relat_1(A_92,B_93),B_94),k2_relat_1(A_92))
      | ~ v1_relat_1(A_92)
      | r1_tarski(k9_relat_1(A_92,B_93),B_94) ) ),
    inference(resolution,[status(thm)],[c_6,c_90])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_146,plain,(
    ! [A_95,B_96] :
      ( ~ v1_relat_1(A_95)
      | r1_tarski(k9_relat_1(A_95,B_96),k2_relat_1(A_95)) ) ),
    inference(resolution,[status(thm)],[c_134,c_4])).

tff(c_30,plain,(
    ~ r1_tarski(k9_relat_1('#skF_7','#skF_6'),k2_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_151,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_146,c_30])).

tff(c_156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_151])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:13:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.22  
% 1.95/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.22  %$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_5 > #skF_3 > #skF_1
% 1.95/1.22  
% 1.95/1.22  %Foreground sorts:
% 1.95/1.22  
% 1.95/1.22  
% 1.95/1.22  %Background operators:
% 1.95/1.22  
% 1.95/1.22  
% 1.95/1.22  %Foreground operators:
% 1.95/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.22  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.95/1.22  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.95/1.22  tff('#skF_7', type, '#skF_7': $i).
% 1.95/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.95/1.22  tff('#skF_6', type, '#skF_6': $i).
% 1.95/1.22  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.95/1.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.95/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.22  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 1.95/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.95/1.22  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.95/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.95/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.95/1.22  
% 1.95/1.23  tff(f_58, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 1.95/1.23  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.95/1.23  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(E, D), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_relat_1)).
% 1.95/1.23  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 1.95/1.23  tff(c_32, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.95/1.23  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.95/1.23  tff(c_75, plain, (![A_83, B_84, D_85]: (r2_hidden(k4_tarski('#skF_5'(A_83, B_84, k9_relat_1(A_83, B_84), D_85), D_85), A_83) | ~r2_hidden(D_85, k9_relat_1(A_83, B_84)) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.95/1.23  tff(c_26, plain, (![B_49, C_50, A_48]: (r2_hidden(B_49, k2_relat_1(C_50)) | ~r2_hidden(k4_tarski(A_48, B_49), C_50) | ~v1_relat_1(C_50))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.95/1.23  tff(c_90, plain, (![D_86, A_87, B_88]: (r2_hidden(D_86, k2_relat_1(A_87)) | ~r2_hidden(D_86, k9_relat_1(A_87, B_88)) | ~v1_relat_1(A_87))), inference(resolution, [status(thm)], [c_75, c_26])).
% 1.95/1.23  tff(c_134, plain, (![A_92, B_93, B_94]: (r2_hidden('#skF_1'(k9_relat_1(A_92, B_93), B_94), k2_relat_1(A_92)) | ~v1_relat_1(A_92) | r1_tarski(k9_relat_1(A_92, B_93), B_94))), inference(resolution, [status(thm)], [c_6, c_90])).
% 1.95/1.23  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.95/1.23  tff(c_146, plain, (![A_95, B_96]: (~v1_relat_1(A_95) | r1_tarski(k9_relat_1(A_95, B_96), k2_relat_1(A_95)))), inference(resolution, [status(thm)], [c_134, c_4])).
% 1.95/1.23  tff(c_30, plain, (~r1_tarski(k9_relat_1('#skF_7', '#skF_6'), k2_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.95/1.23  tff(c_151, plain, (~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_146, c_30])).
% 1.95/1.23  tff(c_156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_151])).
% 1.95/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.23  
% 1.95/1.23  Inference rules
% 1.95/1.23  ----------------------
% 1.95/1.23  #Ref     : 0
% 1.95/1.23  #Sup     : 28
% 1.95/1.23  #Fact    : 0
% 1.95/1.23  #Define  : 0
% 1.95/1.23  #Split   : 0
% 1.95/1.23  #Chain   : 0
% 1.95/1.23  #Close   : 0
% 1.95/1.23  
% 1.95/1.23  Ordering : KBO
% 1.95/1.23  
% 1.95/1.23  Simplification rules
% 1.95/1.23  ----------------------
% 1.95/1.23  #Subsume      : 1
% 1.95/1.23  #Demod        : 1
% 1.95/1.23  #Tautology    : 1
% 1.95/1.23  #SimpNegUnit  : 0
% 1.95/1.23  #BackRed      : 0
% 1.95/1.23  
% 1.95/1.23  #Partial instantiations: 0
% 1.95/1.23  #Strategies tried      : 1
% 1.95/1.23  
% 1.95/1.23  Timing (in seconds)
% 1.95/1.23  ----------------------
% 1.95/1.23  Preprocessing        : 0.29
% 1.95/1.23  Parsing              : 0.15
% 1.95/1.23  CNF conversion       : 0.03
% 1.95/1.23  Main loop            : 0.17
% 1.95/1.23  Inferencing          : 0.07
% 1.95/1.23  Reduction            : 0.04
% 1.95/1.23  Demodulation         : 0.03
% 1.95/1.23  BG Simplification    : 0.02
% 1.95/1.23  Subsumption          : 0.04
% 1.95/1.23  Abstraction          : 0.01
% 1.95/1.23  MUC search           : 0.00
% 1.95/1.23  Cooper               : 0.00
% 1.95/1.23  Total                : 0.49
% 1.95/1.23  Index Insertion      : 0.00
% 1.95/1.23  Index Deletion       : 0.00
% 1.95/1.23  Index Matching       : 0.00
% 1.95/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
