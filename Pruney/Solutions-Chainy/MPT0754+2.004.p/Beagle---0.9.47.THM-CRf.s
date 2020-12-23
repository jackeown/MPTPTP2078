%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:30 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   30 (  38 expanded)
%              Number of leaves         :   15 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 ( 103 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r1_tarski > v5_ordinal1 > v1_relat_1 > v1_funct_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => ! [C] :
            ( ( v1_relat_1(C)
              & v5_relat_1(C,A)
              & v1_funct_1(C)
              & v5_ordinal1(C) )
           => ( v1_relat_1(C)
              & v5_relat_1(C,B)
              & v1_funct_1(C)
              & v5_ordinal1(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_ordinal1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_14,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_27,plain,(
    ! [A_11,C_12,B_13] :
      ( r1_tarski(A_11,C_12)
      | ~ r1_tarski(B_13,C_12)
      | ~ r1_tarski(A_11,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    ! [A_14] :
      ( r1_tarski(A_14,'#skF_2')
      | ~ r1_tarski(A_14,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_18,c_27])).

tff(c_4,plain,(
    ! [B_5,A_4] :
      ( v5_relat_1(B_5,A_4)
      | ~ r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_54,plain,(
    ! [B_17] :
      ( v5_relat_1(B_17,'#skF_2')
      | ~ v1_relat_1(B_17)
      | ~ r1_tarski(k2_relat_1(B_17),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_4])).

tff(c_60,plain,(
    ! [B_18] :
      ( v5_relat_1(B_18,'#skF_2')
      | ~ v5_relat_1(B_18,'#skF_1')
      | ~ v1_relat_1(B_18) ) ),
    inference(resolution,[status(thm)],[c_6,c_54])).

tff(c_12,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10,plain,(
    v5_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,
    ( ~ v5_ordinal1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_20,plain,(
    ~ v5_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_12,c_10,c_8])).

tff(c_63,plain,
    ( ~ v5_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_20])).

tff(c_67,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_63])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:08:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.10  
% 1.70/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.10  %$ v5_relat_1 > r1_tarski > v5_ordinal1 > v1_relat_1 > v1_funct_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.70/1.10  
% 1.70/1.10  %Foreground sorts:
% 1.70/1.10  
% 1.70/1.10  
% 1.70/1.10  %Background operators:
% 1.70/1.10  
% 1.70/1.10  
% 1.70/1.10  %Foreground operators:
% 1.70/1.10  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.70/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.70/1.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.70/1.10  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 1.70/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.70/1.10  tff('#skF_3', type, '#skF_3': $i).
% 1.70/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.70/1.10  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.70/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.70/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.10  
% 1.70/1.11  tff(f_57, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => (![C]: ((((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) & v5_ordinal1(C)) => (((v1_relat_1(C) & v5_relat_1(C, B)) & v1_funct_1(C)) & v5_ordinal1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_ordinal1)).
% 1.70/1.11  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 1.70/1.11  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.70/1.11  tff(c_16, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.70/1.11  tff(c_14, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.70/1.11  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.70/1.11  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.70/1.11  tff(c_27, plain, (![A_11, C_12, B_13]: (r1_tarski(A_11, C_12) | ~r1_tarski(B_13, C_12) | ~r1_tarski(A_11, B_13))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.70/1.11  tff(c_34, plain, (![A_14]: (r1_tarski(A_14, '#skF_2') | ~r1_tarski(A_14, '#skF_1'))), inference(resolution, [status(thm)], [c_18, c_27])).
% 1.70/1.11  tff(c_4, plain, (![B_5, A_4]: (v5_relat_1(B_5, A_4) | ~r1_tarski(k2_relat_1(B_5), A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.70/1.11  tff(c_54, plain, (![B_17]: (v5_relat_1(B_17, '#skF_2') | ~v1_relat_1(B_17) | ~r1_tarski(k2_relat_1(B_17), '#skF_1'))), inference(resolution, [status(thm)], [c_34, c_4])).
% 1.70/1.11  tff(c_60, plain, (![B_18]: (v5_relat_1(B_18, '#skF_2') | ~v5_relat_1(B_18, '#skF_1') | ~v1_relat_1(B_18))), inference(resolution, [status(thm)], [c_6, c_54])).
% 1.70/1.11  tff(c_12, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.70/1.11  tff(c_10, plain, (v5_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.70/1.11  tff(c_8, plain, (~v5_ordinal1('#skF_3') | ~v1_funct_1('#skF_3') | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.70/1.11  tff(c_20, plain, (~v5_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_12, c_10, c_8])).
% 1.70/1.11  tff(c_63, plain, (~v5_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_20])).
% 1.70/1.11  tff(c_67, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_63])).
% 1.70/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.11  
% 1.70/1.11  Inference rules
% 1.70/1.11  ----------------------
% 1.70/1.11  #Ref     : 0
% 1.70/1.11  #Sup     : 10
% 1.70/1.11  #Fact    : 0
% 1.70/1.11  #Define  : 0
% 1.70/1.11  #Split   : 0
% 1.70/1.11  #Chain   : 0
% 1.70/1.11  #Close   : 0
% 1.70/1.11  
% 1.70/1.11  Ordering : KBO
% 1.70/1.11  
% 1.70/1.11  Simplification rules
% 1.70/1.11  ----------------------
% 1.70/1.11  #Subsume      : 1
% 1.70/1.11  #Demod        : 6
% 1.70/1.11  #Tautology    : 2
% 1.70/1.11  #SimpNegUnit  : 0
% 1.70/1.11  #BackRed      : 0
% 1.70/1.11  
% 1.70/1.11  #Partial instantiations: 0
% 1.70/1.11  #Strategies tried      : 1
% 1.70/1.11  
% 1.70/1.11  Timing (in seconds)
% 1.70/1.11  ----------------------
% 1.70/1.12  Preprocessing        : 0.26
% 1.70/1.12  Parsing              : 0.15
% 1.70/1.12  CNF conversion       : 0.02
% 1.70/1.12  Main loop            : 0.11
% 1.70/1.12  Inferencing          : 0.05
% 1.70/1.12  Reduction            : 0.03
% 1.70/1.12  Demodulation         : 0.02
% 1.70/1.12  BG Simplification    : 0.01
% 1.70/1.12  Subsumption          : 0.02
% 1.70/1.12  Abstraction          : 0.00
% 1.70/1.12  MUC search           : 0.00
% 1.70/1.12  Cooper               : 0.00
% 1.70/1.12  Total                : 0.39
% 1.70/1.12  Index Insertion      : 0.00
% 1.70/1.12  Index Deletion       : 0.00
% 1.70/1.12  Index Matching       : 0.00
% 1.70/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
