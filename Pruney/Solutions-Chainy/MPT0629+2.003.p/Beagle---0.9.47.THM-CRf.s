%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:17 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   34 (  37 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 (  63 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ( r2_hidden(A,k2_relat_1(k5_relat_1(C,B)))
             => r2_hidden(A,k2_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_funct_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k7_relat_1(B,A)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_14,plain,(
    ~ r2_hidden('#skF_2',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_20,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_76,plain,(
    ! [B_32,A_33] :
      ( k9_relat_1(B_32,k2_relat_1(A_33)) = k2_relat_1(k5_relat_1(A_33,B_32))
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( k2_relat_1(k7_relat_1(B_7,A_6)) = k9_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_49,plain,(
    ! [B_24,A_25] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_24,A_25)),k2_relat_1(B_24))
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_52,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k9_relat_1(B_7,A_6),k2_relat_1(B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_49])).

tff(c_101,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_38,B_39)),k2_relat_1(B_39))
      | ~ v1_relat_1(B_39)
      | ~ v1_relat_1(B_39)
      | ~ v1_relat_1(B_39)
      | ~ v1_relat_1(A_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_52])).

tff(c_16,plain,(
    r2_hidden('#skF_2',k2_relat_1(k5_relat_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_42,plain,(
    ! [C_21,B_22,A_23] :
      ( r2_hidden(C_21,B_22)
      | ~ r2_hidden(C_21,A_23)
      | ~ r1_tarski(A_23,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_48,plain,(
    ! [B_22] :
      ( r2_hidden('#skF_2',B_22)
      | ~ r1_tarski(k2_relat_1(k5_relat_1('#skF_4','#skF_3')),B_22) ) ),
    inference(resolution,[status(thm)],[c_16,c_42])).

tff(c_107,plain,
    ( r2_hidden('#skF_2',k2_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_101,c_48])).

tff(c_114,plain,(
    r2_hidden('#skF_2',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_24,c_107])).

tff(c_116,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_114])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:06:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.25  
% 1.92/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.25  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.92/1.25  
% 1.92/1.25  %Foreground sorts:
% 1.92/1.25  
% 1.92/1.25  
% 1.92/1.25  %Background operators:
% 1.92/1.25  
% 1.92/1.25  
% 1.92/1.25  %Foreground operators:
% 1.92/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.92/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.92/1.25  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.92/1.25  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.92/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.92/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.92/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.92/1.25  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.92/1.25  tff('#skF_3', type, '#skF_3': $i).
% 1.92/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.92/1.25  tff('#skF_4', type, '#skF_4': $i).
% 1.92/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.92/1.25  
% 1.92/1.26  tff(f_61, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k2_relat_1(k5_relat_1(C, B))) => r2_hidden(A, k2_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_funct_1)).
% 1.92/1.26  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 1.92/1.26  tff(f_36, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.92/1.26  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k7_relat_1(B, A)), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_relat_1)).
% 1.92/1.26  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.92/1.26  tff(c_14, plain, (~r2_hidden('#skF_2', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.92/1.26  tff(c_20, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.92/1.26  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.92/1.26  tff(c_76, plain, (![B_32, A_33]: (k9_relat_1(B_32, k2_relat_1(A_33))=k2_relat_1(k5_relat_1(A_33, B_32)) | ~v1_relat_1(B_32) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.92/1.26  tff(c_8, plain, (![B_7, A_6]: (k2_relat_1(k7_relat_1(B_7, A_6))=k9_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.92/1.26  tff(c_49, plain, (![B_24, A_25]: (r1_tarski(k2_relat_1(k7_relat_1(B_24, A_25)), k2_relat_1(B_24)) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.92/1.26  tff(c_52, plain, (![B_7, A_6]: (r1_tarski(k9_relat_1(B_7, A_6), k2_relat_1(B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(B_7))), inference(superposition, [status(thm), theory('equality')], [c_8, c_49])).
% 1.92/1.26  tff(c_101, plain, (![A_38, B_39]: (r1_tarski(k2_relat_1(k5_relat_1(A_38, B_39)), k2_relat_1(B_39)) | ~v1_relat_1(B_39) | ~v1_relat_1(B_39) | ~v1_relat_1(B_39) | ~v1_relat_1(A_38))), inference(superposition, [status(thm), theory('equality')], [c_76, c_52])).
% 1.92/1.26  tff(c_16, plain, (r2_hidden('#skF_2', k2_relat_1(k5_relat_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.92/1.26  tff(c_42, plain, (![C_21, B_22, A_23]: (r2_hidden(C_21, B_22) | ~r2_hidden(C_21, A_23) | ~r1_tarski(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.92/1.26  tff(c_48, plain, (![B_22]: (r2_hidden('#skF_2', B_22) | ~r1_tarski(k2_relat_1(k5_relat_1('#skF_4', '#skF_3')), B_22))), inference(resolution, [status(thm)], [c_16, c_42])).
% 1.92/1.26  tff(c_107, plain, (r2_hidden('#skF_2', k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_101, c_48])).
% 1.92/1.26  tff(c_114, plain, (r2_hidden('#skF_2', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_24, c_107])).
% 1.92/1.26  tff(c_116, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_114])).
% 1.92/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.26  
% 1.92/1.26  Inference rules
% 1.92/1.26  ----------------------
% 1.92/1.26  #Ref     : 0
% 1.92/1.26  #Sup     : 21
% 1.92/1.26  #Fact    : 0
% 1.92/1.26  #Define  : 0
% 1.92/1.26  #Split   : 0
% 1.92/1.26  #Chain   : 0
% 1.92/1.26  #Close   : 0
% 1.92/1.26  
% 1.92/1.26  Ordering : KBO
% 1.92/1.26  
% 1.92/1.26  Simplification rules
% 1.92/1.26  ----------------------
% 1.92/1.26  #Subsume      : 1
% 1.92/1.26  #Demod        : 3
% 1.92/1.26  #Tautology    : 6
% 1.92/1.26  #SimpNegUnit  : 1
% 1.92/1.26  #BackRed      : 0
% 1.92/1.26  
% 1.92/1.26  #Partial instantiations: 0
% 1.92/1.26  #Strategies tried      : 1
% 1.92/1.26  
% 1.92/1.26  Timing (in seconds)
% 1.92/1.26  ----------------------
% 1.92/1.27  Preprocessing        : 0.29
% 1.92/1.27  Parsing              : 0.15
% 1.92/1.27  CNF conversion       : 0.02
% 1.92/1.27  Main loop            : 0.20
% 1.92/1.27  Inferencing          : 0.09
% 1.92/1.27  Reduction            : 0.04
% 1.92/1.27  Demodulation         : 0.03
% 1.92/1.27  BG Simplification    : 0.01
% 1.92/1.27  Subsumption          : 0.03
% 1.92/1.27  Abstraction          : 0.01
% 1.92/1.27  MUC search           : 0.00
% 1.92/1.27  Cooper               : 0.00
% 1.92/1.27  Total                : 0.51
% 1.92/1.27  Index Insertion      : 0.00
% 1.92/1.27  Index Deletion       : 0.00
% 1.92/1.27  Index Matching       : 0.00
% 1.92/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
