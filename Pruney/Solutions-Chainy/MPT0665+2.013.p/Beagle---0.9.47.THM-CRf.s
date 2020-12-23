%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:16 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   37 (  43 expanded)
%              Number of leaves         :   23 (  28 expanded)
%              Depth                    :    5
%              Number of atoms          :   46 (  72 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r2_hidden(A,k1_relat_1(C))
            & r2_hidden(A,B) )
         => r2_hidden(k1_funct_1(C,A),k2_relat_1(k7_relat_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_funct_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_38,axiom,(
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

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_34,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_32,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_80,plain,(
    ! [A_64,C_65] :
      ( r2_hidden(k4_tarski(A_64,k1_funct_1(C_65,A_64)),C_65)
      | ~ r2_hidden(A_64,k1_relat_1(C_65))
      | ~ v1_funct_1(C_65)
      | ~ v1_relat_1(C_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_30,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_53,plain,(
    ! [D_56,A_57,B_58,E_59] :
      ( r2_hidden(D_56,k9_relat_1(A_57,B_58))
      | ~ r2_hidden(E_59,B_58)
      | ~ r2_hidden(k4_tarski(E_59,D_56),A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_59,plain,(
    ! [D_56,A_57] :
      ( r2_hidden(D_56,k9_relat_1(A_57,'#skF_6'))
      | ~ r2_hidden(k4_tarski('#skF_5',D_56),A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(resolution,[status(thm)],[c_30,c_53])).

tff(c_98,plain,(
    ! [C_66] :
      ( r2_hidden(k1_funct_1(C_66,'#skF_5'),k9_relat_1(C_66,'#skF_6'))
      | ~ r2_hidden('#skF_5',k1_relat_1(C_66))
      | ~ v1_funct_1(C_66)
      | ~ v1_relat_1(C_66) ) ),
    inference(resolution,[status(thm)],[c_80,c_59])).

tff(c_37,plain,(
    ! [B_48,A_49] :
      ( k2_relat_1(k7_relat_1(B_48,A_49)) = k9_relat_1(B_48,A_49)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_28,plain,(
    ~ r2_hidden(k1_funct_1('#skF_7','#skF_5'),k2_relat_1(k7_relat_1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_43,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_7','#skF_5'),k9_relat_1('#skF_7','#skF_6'))
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_28])).

tff(c_49,plain,(
    ~ r2_hidden(k1_funct_1('#skF_7','#skF_5'),k9_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_43])).

tff(c_103,plain,
    ( ~ r2_hidden('#skF_5',k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_98,c_49])).

tff(c_108,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_103])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:50:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.28  
% 1.89/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.29  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 1.89/1.29  
% 1.89/1.29  %Foreground sorts:
% 1.89/1.29  
% 1.89/1.29  
% 1.89/1.29  %Background operators:
% 1.89/1.29  
% 1.89/1.29  
% 1.89/1.29  %Foreground operators:
% 1.89/1.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.89/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.89/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.89/1.29  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.89/1.29  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.89/1.29  tff('#skF_7', type, '#skF_7': $i).
% 1.89/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.89/1.29  tff('#skF_5', type, '#skF_5': $i).
% 1.89/1.29  tff('#skF_6', type, '#skF_6': $i).
% 1.89/1.29  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.89/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.89/1.29  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.89/1.29  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 1.89/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.89/1.29  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.89/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.89/1.29  
% 1.89/1.30  tff(f_63, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(A, B)) => r2_hidden(k1_funct_1(C, A), k2_relat_1(k7_relat_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_funct_1)).
% 1.89/1.30  tff(f_52, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 1.89/1.30  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(E, D), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_relat_1)).
% 1.89/1.30  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.89/1.30  tff(c_36, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.89/1.30  tff(c_34, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.89/1.30  tff(c_32, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.89/1.30  tff(c_80, plain, (![A_64, C_65]: (r2_hidden(k4_tarski(A_64, k1_funct_1(C_65, A_64)), C_65) | ~r2_hidden(A_64, k1_relat_1(C_65)) | ~v1_funct_1(C_65) | ~v1_relat_1(C_65))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.89/1.30  tff(c_30, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.89/1.30  tff(c_53, plain, (![D_56, A_57, B_58, E_59]: (r2_hidden(D_56, k9_relat_1(A_57, B_58)) | ~r2_hidden(E_59, B_58) | ~r2_hidden(k4_tarski(E_59, D_56), A_57) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.89/1.30  tff(c_59, plain, (![D_56, A_57]: (r2_hidden(D_56, k9_relat_1(A_57, '#skF_6')) | ~r2_hidden(k4_tarski('#skF_5', D_56), A_57) | ~v1_relat_1(A_57))), inference(resolution, [status(thm)], [c_30, c_53])).
% 1.89/1.30  tff(c_98, plain, (![C_66]: (r2_hidden(k1_funct_1(C_66, '#skF_5'), k9_relat_1(C_66, '#skF_6')) | ~r2_hidden('#skF_5', k1_relat_1(C_66)) | ~v1_funct_1(C_66) | ~v1_relat_1(C_66))), inference(resolution, [status(thm)], [c_80, c_59])).
% 1.89/1.30  tff(c_37, plain, (![B_48, A_49]: (k2_relat_1(k7_relat_1(B_48, A_49))=k9_relat_1(B_48, A_49) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.89/1.30  tff(c_28, plain, (~r2_hidden(k1_funct_1('#skF_7', '#skF_5'), k2_relat_1(k7_relat_1('#skF_7', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.89/1.30  tff(c_43, plain, (~r2_hidden(k1_funct_1('#skF_7', '#skF_5'), k9_relat_1('#skF_7', '#skF_6')) | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_37, c_28])).
% 1.89/1.30  tff(c_49, plain, (~r2_hidden(k1_funct_1('#skF_7', '#skF_5'), k9_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_43])).
% 1.89/1.30  tff(c_103, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_98, c_49])).
% 1.89/1.30  tff(c_108, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_103])).
% 1.89/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.30  
% 1.89/1.30  Inference rules
% 1.89/1.30  ----------------------
% 1.89/1.30  #Ref     : 0
% 1.89/1.30  #Sup     : 15
% 1.89/1.30  #Fact    : 0
% 1.89/1.30  #Define  : 0
% 1.89/1.30  #Split   : 0
% 1.89/1.30  #Chain   : 0
% 1.89/1.30  #Close   : 0
% 1.89/1.30  
% 1.89/1.30  Ordering : KBO
% 1.89/1.30  
% 1.89/1.30  Simplification rules
% 1.89/1.30  ----------------------
% 1.89/1.30  #Subsume      : 0
% 1.89/1.30  #Demod        : 4
% 1.89/1.30  #Tautology    : 4
% 1.89/1.30  #SimpNegUnit  : 0
% 1.89/1.30  #BackRed      : 0
% 1.89/1.30  
% 1.89/1.30  #Partial instantiations: 0
% 1.89/1.30  #Strategies tried      : 1
% 1.89/1.30  
% 1.89/1.30  Timing (in seconds)
% 1.89/1.30  ----------------------
% 1.89/1.30  Preprocessing        : 0.34
% 1.89/1.30  Parsing              : 0.16
% 1.89/1.30  CNF conversion       : 0.03
% 1.89/1.30  Main loop            : 0.15
% 1.89/1.30  Inferencing          : 0.05
% 1.89/1.30  Reduction            : 0.04
% 1.89/1.30  Demodulation         : 0.03
% 1.89/1.30  BG Simplification    : 0.02
% 2.08/1.30  Subsumption          : 0.03
% 2.08/1.30  Abstraction          : 0.01
% 2.08/1.30  MUC search           : 0.00
% 2.08/1.30  Cooper               : 0.00
% 2.08/1.30  Total                : 0.52
% 2.08/1.30  Index Insertion      : 0.00
% 2.08/1.30  Index Deletion       : 0.00
% 2.08/1.30  Index Matching       : 0.00
% 2.08/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
