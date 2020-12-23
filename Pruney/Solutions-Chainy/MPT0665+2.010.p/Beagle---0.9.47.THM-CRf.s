%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:15 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   38 (  44 expanded)
%              Number of leaves         :   23 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   60 (  86 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r2_hidden(A,k1_relat_1(C))
            & r2_hidden(A,B) )
         => r2_hidden(k1_funct_1(C,A),k2_relat_1(k7_relat_1(C,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( v1_relat_1(C)
         => ( C = k7_relat_1(A,B)
          <=> ! [D,E] :
                ( r2_hidden(k4_tarski(D,E),C)
              <=> ( r2_hidden(D,B)
                  & r2_hidden(k4_tarski(D,E),A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_20,plain,(
    ! [A_20,B_21] :
      ( v1_relat_1(k7_relat_1(A_20,B_21))
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_38,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_36,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_34,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    ! [A_25,C_27] :
      ( r2_hidden(k4_tarski(A_25,k1_funct_1(C_27,A_25)),C_27)
      | ~ r2_hidden(A_25,k1_relat_1(C_27))
      | ~ v1_funct_1(C_27)
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_78,plain,(
    ! [D_54,E_55,A_56,B_57] :
      ( r2_hidden(k4_tarski(D_54,E_55),k7_relat_1(A_56,B_57))
      | ~ r2_hidden(k4_tarski(D_54,E_55),A_56)
      | ~ r2_hidden(D_54,B_57)
      | ~ v1_relat_1(k7_relat_1(A_56,B_57))
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [B_23,C_24,A_22] :
      ( r2_hidden(B_23,k2_relat_1(C_24))
      | ~ r2_hidden(k4_tarski(A_22,B_23),C_24)
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_137,plain,(
    ! [E_65,A_66,B_67,D_68] :
      ( r2_hidden(E_65,k2_relat_1(k7_relat_1(A_66,B_67)))
      | ~ r2_hidden(k4_tarski(D_68,E_65),A_66)
      | ~ r2_hidden(D_68,B_67)
      | ~ v1_relat_1(k7_relat_1(A_66,B_67))
      | ~ v1_relat_1(A_66) ) ),
    inference(resolution,[status(thm)],[c_78,c_22])).

tff(c_203,plain,(
    ! [C_81,A_82,B_83] :
      ( r2_hidden(k1_funct_1(C_81,A_82),k2_relat_1(k7_relat_1(C_81,B_83)))
      | ~ r2_hidden(A_82,B_83)
      | ~ v1_relat_1(k7_relat_1(C_81,B_83))
      | ~ r2_hidden(A_82,k1_relat_1(C_81))
      | ~ v1_funct_1(C_81)
      | ~ v1_relat_1(C_81) ) ),
    inference(resolution,[status(thm)],[c_26,c_137])).

tff(c_32,plain,(
    ~ r2_hidden(k1_funct_1('#skF_7','#skF_5'),k2_relat_1(k7_relat_1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_206,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | ~ v1_relat_1(k7_relat_1('#skF_7','#skF_6'))
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_203,c_32])).

tff(c_209,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_206])).

tff(c_212,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_20,c_209])).

tff(c_216,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_212])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:47:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.34  
% 2.17/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.34  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 2.17/1.34  
% 2.17/1.34  %Foreground sorts:
% 2.17/1.34  
% 2.17/1.34  
% 2.17/1.34  %Background operators:
% 2.17/1.34  
% 2.17/1.34  
% 2.17/1.34  %Foreground operators:
% 2.17/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.17/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.17/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.34  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.17/1.34  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.17/1.34  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.17/1.34  tff('#skF_7', type, '#skF_7': $i).
% 2.17/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.17/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.17/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.17/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.17/1.34  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.17/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.17/1.34  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.17/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.17/1.34  
% 2.17/1.35  tff(f_72, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(A, B)) => r2_hidden(k1_funct_1(C, A), k2_relat_1(k7_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_funct_1)).
% 2.17/1.35  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.17/1.35  tff(f_61, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 2.17/1.35  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (v1_relat_1(C) => ((C = k7_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (r2_hidden(D, B) & r2_hidden(k4_tarski(D, E), A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_relat_1)).
% 2.17/1.35  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 2.17/1.35  tff(c_40, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.17/1.35  tff(c_20, plain, (![A_20, B_21]: (v1_relat_1(k7_relat_1(A_20, B_21)) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.17/1.35  tff(c_38, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.17/1.35  tff(c_36, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.17/1.35  tff(c_34, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.17/1.35  tff(c_26, plain, (![A_25, C_27]: (r2_hidden(k4_tarski(A_25, k1_funct_1(C_27, A_25)), C_27) | ~r2_hidden(A_25, k1_relat_1(C_27)) | ~v1_funct_1(C_27) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.17/1.35  tff(c_78, plain, (![D_54, E_55, A_56, B_57]: (r2_hidden(k4_tarski(D_54, E_55), k7_relat_1(A_56, B_57)) | ~r2_hidden(k4_tarski(D_54, E_55), A_56) | ~r2_hidden(D_54, B_57) | ~v1_relat_1(k7_relat_1(A_56, B_57)) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.17/1.35  tff(c_22, plain, (![B_23, C_24, A_22]: (r2_hidden(B_23, k2_relat_1(C_24)) | ~r2_hidden(k4_tarski(A_22, B_23), C_24) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.17/1.35  tff(c_137, plain, (![E_65, A_66, B_67, D_68]: (r2_hidden(E_65, k2_relat_1(k7_relat_1(A_66, B_67))) | ~r2_hidden(k4_tarski(D_68, E_65), A_66) | ~r2_hidden(D_68, B_67) | ~v1_relat_1(k7_relat_1(A_66, B_67)) | ~v1_relat_1(A_66))), inference(resolution, [status(thm)], [c_78, c_22])).
% 2.17/1.35  tff(c_203, plain, (![C_81, A_82, B_83]: (r2_hidden(k1_funct_1(C_81, A_82), k2_relat_1(k7_relat_1(C_81, B_83))) | ~r2_hidden(A_82, B_83) | ~v1_relat_1(k7_relat_1(C_81, B_83)) | ~r2_hidden(A_82, k1_relat_1(C_81)) | ~v1_funct_1(C_81) | ~v1_relat_1(C_81))), inference(resolution, [status(thm)], [c_26, c_137])).
% 2.17/1.35  tff(c_32, plain, (~r2_hidden(k1_funct_1('#skF_7', '#skF_5'), k2_relat_1(k7_relat_1('#skF_7', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.17/1.35  tff(c_206, plain, (~r2_hidden('#skF_5', '#skF_6') | ~v1_relat_1(k7_relat_1('#skF_7', '#skF_6')) | ~r2_hidden('#skF_5', k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_203, c_32])).
% 2.17/1.35  tff(c_209, plain, (~v1_relat_1(k7_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_206])).
% 2.17/1.35  tff(c_212, plain, (~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_20, c_209])).
% 2.17/1.35  tff(c_216, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_212])).
% 2.17/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.35  
% 2.17/1.35  Inference rules
% 2.17/1.35  ----------------------
% 2.17/1.35  #Ref     : 0
% 2.17/1.35  #Sup     : 36
% 2.17/1.35  #Fact    : 0
% 2.17/1.35  #Define  : 0
% 2.17/1.35  #Split   : 0
% 2.17/1.35  #Chain   : 0
% 2.17/1.35  #Close   : 0
% 2.17/1.35  
% 2.17/1.35  Ordering : KBO
% 2.17/1.35  
% 2.17/1.35  Simplification rules
% 2.17/1.35  ----------------------
% 2.17/1.35  #Subsume      : 1
% 2.17/1.35  #Demod        : 5
% 2.17/1.35  #Tautology    : 5
% 2.17/1.35  #SimpNegUnit  : 0
% 2.17/1.35  #BackRed      : 0
% 2.17/1.35  
% 2.17/1.35  #Partial instantiations: 0
% 2.17/1.35  #Strategies tried      : 1
% 2.17/1.35  
% 2.17/1.35  Timing (in seconds)
% 2.17/1.35  ----------------------
% 2.17/1.35  Preprocessing        : 0.31
% 2.17/1.35  Parsing              : 0.17
% 2.17/1.35  CNF conversion       : 0.03
% 2.17/1.35  Main loop            : 0.22
% 2.17/1.35  Inferencing          : 0.09
% 2.17/1.35  Reduction            : 0.05
% 2.17/1.35  Demodulation         : 0.04
% 2.17/1.35  BG Simplification    : 0.02
% 2.17/1.36  Subsumption          : 0.05
% 2.17/1.36  Abstraction          : 0.01
% 2.17/1.36  MUC search           : 0.00
% 2.17/1.36  Cooper               : 0.00
% 2.17/1.36  Total                : 0.55
% 2.17/1.36  Index Insertion      : 0.00
% 2.17/1.36  Index Deletion       : 0.00
% 2.17/1.36  Index Matching       : 0.00
% 2.17/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
