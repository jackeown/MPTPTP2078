%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:36 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   34 (  42 expanded)
%              Number of leaves         :   21 (  27 expanded)
%              Depth                    :    5
%              Number of atoms          :   48 ( 116 expanded)
%              Number of equality atoms :    1 (   7 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v8_relat_2 > v6_relat_2 > v4_relat_2 > v2_wellord1 > v1_wellord1 > v1_relat_2 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > #skF_5 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(v6_relat_2,type,(
    v6_relat_2: $i > $o )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(v1_wellord1,type,(
    v1_wellord1: $i > $o )).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( v2_wellord1(A)
         => ! [B] :
              ~ ( r2_hidden(B,k3_relat_1(A))
                & ? [C] :
                    ( r2_hidden(C,k3_relat_1(A))
                    & ~ r2_hidden(k4_tarski(C,B),A) )
                & ! [C] :
                    ~ ( r2_hidden(C,k3_relat_1(A))
                      & r2_hidden(k4_tarski(B,C),A)
                      & ! [D] :
                          ~ ( r2_hidden(D,k3_relat_1(A))
                            & r2_hidden(k4_tarski(B,D),A)
                            & D != B
                            & ~ r2_hidden(k4_tarski(C,D),A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_wellord1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
      <=> ( v1_relat_2(A)
          & v8_relat_2(A)
          & v4_relat_2(A)
          & v6_relat_2(A)
          & v1_wellord1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v1_relat_2(A)
      <=> ! [B] :
            ( r2_hidden(B,k3_relat_1(A))
           => r2_hidden(k4_tarski(B,B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_wellord1)).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_26,plain,(
    v2_wellord1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_39,plain,(
    ! [A_23] :
      ( v1_relat_2(A_23)
      | ~ v2_wellord1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_42,plain,
    ( v1_relat_2('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_39])).

tff(c_45,plain,(
    v1_relat_2('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_42])).

tff(c_24,plain,(
    r2_hidden('#skF_3',k3_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_14,plain,(
    ! [B_5,A_2] :
      ( r2_hidden(k4_tarski(B_5,B_5),A_2)
      | ~ r2_hidden(B_5,k3_relat_1(A_2))
      | ~ v1_relat_2(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_77,plain,(
    ! [C_34] :
      ( r2_hidden(k4_tarski('#skF_3','#skF_5'(C_34)),'#skF_2')
      | ~ r2_hidden(k4_tarski('#skF_3',C_34),'#skF_2')
      | ~ r2_hidden(C_34,k3_relat_1('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_30,plain,(
    ! [C_19] :
      ( ~ r2_hidden(k4_tarski(C_19,'#skF_5'(C_19)),'#skF_2')
      | ~ r2_hidden(k4_tarski('#skF_3',C_19),'#skF_2')
      | ~ r2_hidden(C_19,k3_relat_1('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_81,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_3'),'#skF_2')
    | ~ r2_hidden('#skF_3',k3_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_77,c_30])).

tff(c_87,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_81])).

tff(c_91,plain,
    ( ~ r2_hidden('#skF_3',k3_relat_1('#skF_2'))
    | ~ v1_relat_2('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_87])).

tff(c_95,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_45,c_24,c_91])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:22:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.17  
% 1.88/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.18  %$ r2_hidden > v8_relat_2 > v6_relat_2 > v4_relat_2 > v2_wellord1 > v1_wellord1 > v1_relat_2 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > #skF_5 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 1.88/1.18  
% 1.88/1.18  %Foreground sorts:
% 1.88/1.18  
% 1.88/1.18  
% 1.88/1.18  %Background operators:
% 1.88/1.18  
% 1.88/1.18  
% 1.88/1.18  %Foreground operators:
% 1.88/1.18  tff('#skF_5', type, '#skF_5': $i > $i).
% 1.88/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.88/1.18  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.88/1.18  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.88/1.18  tff(v1_relat_2, type, v1_relat_2: $i > $o).
% 1.88/1.18  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 1.88/1.18  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.88/1.18  tff(v6_relat_2, type, v6_relat_2: $i > $o).
% 1.88/1.18  tff(v4_relat_2, type, v4_relat_2: $i > $o).
% 1.88/1.18  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 1.88/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.88/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.88/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.88/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.18  tff(v1_wellord1, type, v1_wellord1: $i > $o).
% 1.88/1.18  
% 1.88/1.19  tff(f_81, negated_conjecture, ~(![A]: (v1_relat_1(A) => (v2_wellord1(A) => (![B]: ~((r2_hidden(B, k3_relat_1(A)) & (?[C]: (r2_hidden(C, k3_relat_1(A)) & ~r2_hidden(k4_tarski(C, B), A)))) & (![C]: ~((r2_hidden(C, k3_relat_1(A)) & r2_hidden(k4_tarski(B, C), A)) & (![D]: ~(((r2_hidden(D, k3_relat_1(A)) & r2_hidden(k4_tarski(B, D), A)) & ~(D = B)) & ~r2_hidden(k4_tarski(C, D), A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_wellord1)).
% 1.88/1.19  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) <=> ((((v1_relat_2(A) & v8_relat_2(A)) & v4_relat_2(A)) & v6_relat_2(A)) & v1_wellord1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_wellord1)).
% 1.88/1.19  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (v1_relat_2(A) <=> (![B]: (r2_hidden(B, k3_relat_1(A)) => r2_hidden(k4_tarski(B, B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_wellord1)).
% 1.88/1.19  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.88/1.19  tff(c_26, plain, (v2_wellord1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.88/1.19  tff(c_39, plain, (![A_23]: (v1_relat_2(A_23) | ~v2_wellord1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.88/1.19  tff(c_42, plain, (v1_relat_2('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_26, c_39])).
% 1.88/1.19  tff(c_45, plain, (v1_relat_2('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_42])).
% 1.88/1.19  tff(c_24, plain, (r2_hidden('#skF_3', k3_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.88/1.19  tff(c_14, plain, (![B_5, A_2]: (r2_hidden(k4_tarski(B_5, B_5), A_2) | ~r2_hidden(B_5, k3_relat_1(A_2)) | ~v1_relat_2(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.88/1.19  tff(c_77, plain, (![C_34]: (r2_hidden(k4_tarski('#skF_3', '#skF_5'(C_34)), '#skF_2') | ~r2_hidden(k4_tarski('#skF_3', C_34), '#skF_2') | ~r2_hidden(C_34, k3_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.88/1.19  tff(c_30, plain, (![C_19]: (~r2_hidden(k4_tarski(C_19, '#skF_5'(C_19)), '#skF_2') | ~r2_hidden(k4_tarski('#skF_3', C_19), '#skF_2') | ~r2_hidden(C_19, k3_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.88/1.19  tff(c_81, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_3'), '#skF_2') | ~r2_hidden('#skF_3', k3_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_77, c_30])).
% 1.88/1.19  tff(c_87, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_81])).
% 1.88/1.19  tff(c_91, plain, (~r2_hidden('#skF_3', k3_relat_1('#skF_2')) | ~v1_relat_2('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_14, c_87])).
% 1.88/1.19  tff(c_95, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_45, c_24, c_91])).
% 1.88/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.19  
% 1.88/1.19  Inference rules
% 1.88/1.19  ----------------------
% 1.88/1.19  #Ref     : 0
% 1.88/1.19  #Sup     : 8
% 1.88/1.19  #Fact    : 0
% 1.88/1.19  #Define  : 0
% 1.88/1.19  #Split   : 0
% 1.88/1.19  #Chain   : 0
% 1.88/1.19  #Close   : 0
% 1.88/1.19  
% 1.88/1.19  Ordering : KBO
% 1.88/1.19  
% 1.88/1.19  Simplification rules
% 1.88/1.19  ----------------------
% 1.88/1.19  #Subsume      : 0
% 1.88/1.19  #Demod        : 9
% 1.88/1.19  #Tautology    : 2
% 1.88/1.19  #SimpNegUnit  : 0
% 1.88/1.19  #BackRed      : 0
% 1.88/1.19  
% 1.88/1.19  #Partial instantiations: 0
% 1.88/1.19  #Strategies tried      : 1
% 1.88/1.19  
% 1.88/1.19  Timing (in seconds)
% 1.88/1.19  ----------------------
% 1.88/1.19  Preprocessing        : 0.29
% 1.88/1.19  Parsing              : 0.15
% 1.88/1.19  CNF conversion       : 0.02
% 1.88/1.19  Main loop            : 0.14
% 1.88/1.19  Inferencing          : 0.06
% 1.88/1.19  Reduction            : 0.04
% 1.88/1.19  Demodulation         : 0.03
% 1.88/1.19  BG Simplification    : 0.01
% 1.88/1.19  Subsumption          : 0.02
% 1.88/1.19  Abstraction          : 0.00
% 1.88/1.19  MUC search           : 0.00
% 1.88/1.19  Cooper               : 0.00
% 1.88/1.19  Total                : 0.45
% 1.88/1.19  Index Insertion      : 0.00
% 1.88/1.19  Index Deletion       : 0.00
% 1.88/1.19  Index Matching       : 0.00
% 1.88/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
