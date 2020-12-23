%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:17 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   34 (  40 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :    5
%              Number of atoms          :   48 (  74 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r2_hidden(A,k1_relat_1(C))
            & r2_hidden(A,B) )
         => r2_hidden(k1_funct_1(C,A),k2_relat_1(k7_relat_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_funct_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_24,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12,plain,(
    ! [A_9,C_11] :
      ( r2_hidden(k4_tarski(A_9,k1_funct_1(C_11,A_9)),C_11)
      | ~ r2_hidden(A_9,k1_relat_1(C_11))
      | ~ v1_funct_1(C_11)
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_20,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_77,plain,(
    ! [A_34,C_35,B_36,D_37] :
      ( r2_hidden(A_34,k9_relat_1(C_35,B_36))
      | ~ r2_hidden(D_37,B_36)
      | ~ r2_hidden(k4_tarski(D_37,A_34),C_35)
      | ~ r2_hidden(D_37,k1_relat_1(C_35))
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_96,plain,(
    ! [A_38,C_39] :
      ( r2_hidden(A_38,k9_relat_1(C_39,'#skF_3'))
      | ~ r2_hidden(k4_tarski('#skF_2',A_38),C_39)
      | ~ r2_hidden('#skF_2',k1_relat_1(C_39))
      | ~ v1_relat_1(C_39) ) ),
    inference(resolution,[status(thm)],[c_20,c_77])).

tff(c_102,plain,(
    ! [C_40] :
      ( r2_hidden(k1_funct_1(C_40,'#skF_2'),k9_relat_1(C_40,'#skF_3'))
      | ~ r2_hidden('#skF_2',k1_relat_1(C_40))
      | ~ v1_funct_1(C_40)
      | ~ v1_relat_1(C_40) ) ),
    inference(resolution,[status(thm)],[c_12,c_96])).

tff(c_27,plain,(
    ! [B_12,A_13] :
      ( k2_relat_1(k7_relat_1(B_12,A_13)) = k9_relat_1(B_12,A_13)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_18,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),k2_relat_1(k7_relat_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_33,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),k9_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_27,c_18])).

tff(c_39,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),k9_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_33])).

tff(c_109,plain,
    ( ~ r2_hidden('#skF_2',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_102,c_39])).

tff(c_115,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_109])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:55:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.21  
% 1.80/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.21  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 1.92/1.21  
% 1.92/1.21  %Foreground sorts:
% 1.92/1.21  
% 1.92/1.21  
% 1.92/1.21  %Background operators:
% 1.92/1.21  
% 1.92/1.21  
% 1.92/1.21  %Foreground operators:
% 1.92/1.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.92/1.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.92/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.92/1.21  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.92/1.21  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.92/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.92/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.92/1.21  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.92/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.92/1.21  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.92/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.92/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.92/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.92/1.21  
% 1.92/1.22  tff(f_61, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(A, B)) => r2_hidden(k1_funct_1(C, A), k2_relat_1(k7_relat_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_funct_1)).
% 1.92/1.22  tff(f_50, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 1.92/1.22  tff(f_36, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 1.92/1.22  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.92/1.22  tff(c_26, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.92/1.22  tff(c_24, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.92/1.22  tff(c_22, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.92/1.22  tff(c_12, plain, (![A_9, C_11]: (r2_hidden(k4_tarski(A_9, k1_funct_1(C_11, A_9)), C_11) | ~r2_hidden(A_9, k1_relat_1(C_11)) | ~v1_funct_1(C_11) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.92/1.22  tff(c_20, plain, (r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.92/1.22  tff(c_77, plain, (![A_34, C_35, B_36, D_37]: (r2_hidden(A_34, k9_relat_1(C_35, B_36)) | ~r2_hidden(D_37, B_36) | ~r2_hidden(k4_tarski(D_37, A_34), C_35) | ~r2_hidden(D_37, k1_relat_1(C_35)) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.92/1.22  tff(c_96, plain, (![A_38, C_39]: (r2_hidden(A_38, k9_relat_1(C_39, '#skF_3')) | ~r2_hidden(k4_tarski('#skF_2', A_38), C_39) | ~r2_hidden('#skF_2', k1_relat_1(C_39)) | ~v1_relat_1(C_39))), inference(resolution, [status(thm)], [c_20, c_77])).
% 1.92/1.22  tff(c_102, plain, (![C_40]: (r2_hidden(k1_funct_1(C_40, '#skF_2'), k9_relat_1(C_40, '#skF_3')) | ~r2_hidden('#skF_2', k1_relat_1(C_40)) | ~v1_funct_1(C_40) | ~v1_relat_1(C_40))), inference(resolution, [status(thm)], [c_12, c_96])).
% 1.92/1.22  tff(c_27, plain, (![B_12, A_13]: (k2_relat_1(k7_relat_1(B_12, A_13))=k9_relat_1(B_12, A_13) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.92/1.22  tff(c_18, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_2'), k2_relat_1(k7_relat_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.92/1.22  tff(c_33, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_2'), k9_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_27, c_18])).
% 1.92/1.22  tff(c_39, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_2'), k9_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_33])).
% 1.92/1.22  tff(c_109, plain, (~r2_hidden('#skF_2', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_102, c_39])).
% 1.92/1.22  tff(c_115, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_109])).
% 1.92/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.22  
% 1.92/1.22  Inference rules
% 1.92/1.22  ----------------------
% 1.92/1.22  #Ref     : 0
% 1.92/1.22  #Sup     : 20
% 1.92/1.22  #Fact    : 0
% 1.92/1.22  #Define  : 0
% 1.92/1.22  #Split   : 0
% 1.92/1.22  #Chain   : 0
% 1.92/1.22  #Close   : 0
% 1.92/1.22  
% 1.92/1.22  Ordering : KBO
% 1.92/1.22  
% 1.92/1.22  Simplification rules
% 1.92/1.22  ----------------------
% 1.92/1.22  #Subsume      : 1
% 1.92/1.22  #Demod        : 4
% 1.92/1.22  #Tautology    : 4
% 1.92/1.22  #SimpNegUnit  : 0
% 1.92/1.22  #BackRed      : 0
% 1.92/1.22  
% 1.92/1.22  #Partial instantiations: 0
% 1.92/1.22  #Strategies tried      : 1
% 1.92/1.22  
% 1.92/1.22  Timing (in seconds)
% 1.92/1.22  ----------------------
% 1.92/1.22  Preprocessing        : 0.26
% 1.92/1.22  Parsing              : 0.14
% 1.92/1.22  CNF conversion       : 0.02
% 1.92/1.22  Main loop            : 0.15
% 1.92/1.22  Inferencing          : 0.06
% 1.92/1.22  Reduction            : 0.04
% 1.92/1.22  Demodulation         : 0.03
% 1.92/1.22  BG Simplification    : 0.01
% 1.92/1.22  Subsumption          : 0.03
% 1.92/1.22  Abstraction          : 0.01
% 1.92/1.22  MUC search           : 0.00
% 1.92/1.22  Cooper               : 0.00
% 1.92/1.22  Total                : 0.43
% 1.92/1.22  Index Insertion      : 0.00
% 1.92/1.22  Index Deletion       : 0.00
% 1.92/1.22  Index Matching       : 0.00
% 1.92/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
