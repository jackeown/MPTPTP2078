%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:14 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   39 (  45 expanded)
%              Number of leaves         :   24 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   63 (  89 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r2_hidden(A,k1_relat_1(C))
            & r2_hidden(A,B) )
         => r2_hidden(k1_funct_1(C,A),k2_relat_1(k7_relat_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_20,plain,(
    ! [A_20,B_21] :
      ( v1_relat_1(k7_relat_1(A_20,B_21))
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_40,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_38,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_36,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_28,plain,(
    ! [B_28,A_25] :
      ( r2_hidden(k4_tarski(B_28,k1_funct_1(A_25,B_28)),A_25)
      | ~ r2_hidden(B_28,k1_relat_1(A_25))
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_120,plain,(
    ! [D_58,E_59,A_60,B_61] :
      ( r2_hidden(k4_tarski(D_58,E_59),k7_relat_1(A_60,B_61))
      | ~ r2_hidden(k4_tarski(D_58,E_59),A_60)
      | ~ r2_hidden(D_58,B_61)
      | ~ v1_relat_1(k7_relat_1(A_60,B_61))
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [B_23,C_24,A_22] :
      ( r2_hidden(B_23,k2_relat_1(C_24))
      | ~ r2_hidden(k4_tarski(A_22,B_23),C_24)
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_245,plain,(
    ! [E_81,A_82,B_83,D_84] :
      ( r2_hidden(E_81,k2_relat_1(k7_relat_1(A_82,B_83)))
      | ~ r2_hidden(k4_tarski(D_84,E_81),A_82)
      | ~ r2_hidden(D_84,B_83)
      | ~ v1_relat_1(k7_relat_1(A_82,B_83))
      | ~ v1_relat_1(A_82) ) ),
    inference(resolution,[status(thm)],[c_120,c_22])).

tff(c_338,plain,(
    ! [A_97,B_98,B_99] :
      ( r2_hidden(k1_funct_1(A_97,B_98),k2_relat_1(k7_relat_1(A_97,B_99)))
      | ~ r2_hidden(B_98,B_99)
      | ~ v1_relat_1(k7_relat_1(A_97,B_99))
      | ~ r2_hidden(B_98,k1_relat_1(A_97))
      | ~ v1_funct_1(A_97)
      | ~ v1_relat_1(A_97) ) ),
    inference(resolution,[status(thm)],[c_28,c_245])).

tff(c_34,plain,(
    ~ r2_hidden(k1_funct_1('#skF_7','#skF_5'),k2_relat_1(k7_relat_1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_341,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | ~ v1_relat_1(k7_relat_1('#skF_7','#skF_6'))
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_338,c_34])).

tff(c_350,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_341])).

tff(c_353,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_20,c_350])).

tff(c_357,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_353])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:10:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.36  
% 2.60/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.36  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 2.60/1.36  
% 2.60/1.36  %Foreground sorts:
% 2.60/1.36  
% 2.60/1.36  
% 2.60/1.36  %Background operators:
% 2.60/1.36  
% 2.60/1.36  
% 2.60/1.36  %Foreground operators:
% 2.60/1.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.60/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.60/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.60/1.36  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.60/1.36  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.60/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.60/1.36  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.60/1.36  tff('#skF_7', type, '#skF_7': $i).
% 2.60/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.60/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.60/1.36  tff('#skF_6', type, '#skF_6': $i).
% 2.60/1.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.60/1.36  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.60/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.60/1.36  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.60/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.60/1.36  
% 2.60/1.37  tff(f_80, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(A, B)) => r2_hidden(k1_funct_1(C, A), k2_relat_1(k7_relat_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_funct_1)).
% 2.60/1.37  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.60/1.37  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 2.60/1.37  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (v1_relat_1(C) => ((C = k7_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (r2_hidden(D, B) & r2_hidden(k4_tarski(D, E), A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_relat_1)).
% 2.60/1.37  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 2.60/1.37  tff(c_42, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.60/1.37  tff(c_20, plain, (![A_20, B_21]: (v1_relat_1(k7_relat_1(A_20, B_21)) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.60/1.37  tff(c_40, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.60/1.37  tff(c_38, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.60/1.37  tff(c_36, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.60/1.37  tff(c_28, plain, (![B_28, A_25]: (r2_hidden(k4_tarski(B_28, k1_funct_1(A_25, B_28)), A_25) | ~r2_hidden(B_28, k1_relat_1(A_25)) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.60/1.37  tff(c_120, plain, (![D_58, E_59, A_60, B_61]: (r2_hidden(k4_tarski(D_58, E_59), k7_relat_1(A_60, B_61)) | ~r2_hidden(k4_tarski(D_58, E_59), A_60) | ~r2_hidden(D_58, B_61) | ~v1_relat_1(k7_relat_1(A_60, B_61)) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.60/1.37  tff(c_22, plain, (![B_23, C_24, A_22]: (r2_hidden(B_23, k2_relat_1(C_24)) | ~r2_hidden(k4_tarski(A_22, B_23), C_24) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.60/1.37  tff(c_245, plain, (![E_81, A_82, B_83, D_84]: (r2_hidden(E_81, k2_relat_1(k7_relat_1(A_82, B_83))) | ~r2_hidden(k4_tarski(D_84, E_81), A_82) | ~r2_hidden(D_84, B_83) | ~v1_relat_1(k7_relat_1(A_82, B_83)) | ~v1_relat_1(A_82))), inference(resolution, [status(thm)], [c_120, c_22])).
% 2.60/1.37  tff(c_338, plain, (![A_97, B_98, B_99]: (r2_hidden(k1_funct_1(A_97, B_98), k2_relat_1(k7_relat_1(A_97, B_99))) | ~r2_hidden(B_98, B_99) | ~v1_relat_1(k7_relat_1(A_97, B_99)) | ~r2_hidden(B_98, k1_relat_1(A_97)) | ~v1_funct_1(A_97) | ~v1_relat_1(A_97))), inference(resolution, [status(thm)], [c_28, c_245])).
% 2.60/1.37  tff(c_34, plain, (~r2_hidden(k1_funct_1('#skF_7', '#skF_5'), k2_relat_1(k7_relat_1('#skF_7', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.60/1.37  tff(c_341, plain, (~r2_hidden('#skF_5', '#skF_6') | ~v1_relat_1(k7_relat_1('#skF_7', '#skF_6')) | ~r2_hidden('#skF_5', k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_338, c_34])).
% 2.60/1.37  tff(c_350, plain, (~v1_relat_1(k7_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_341])).
% 2.60/1.37  tff(c_353, plain, (~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_20, c_350])).
% 2.60/1.37  tff(c_357, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_353])).
% 2.60/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.37  
% 2.60/1.37  Inference rules
% 2.60/1.37  ----------------------
% 2.60/1.37  #Ref     : 0
% 2.60/1.37  #Sup     : 68
% 2.60/1.37  #Fact    : 0
% 2.60/1.37  #Define  : 0
% 2.60/1.37  #Split   : 0
% 2.60/1.37  #Chain   : 0
% 2.60/1.37  #Close   : 0
% 2.60/1.37  
% 2.60/1.37  Ordering : KBO
% 2.60/1.37  
% 2.60/1.37  Simplification rules
% 2.60/1.37  ----------------------
% 2.60/1.37  #Subsume      : 8
% 2.60/1.37  #Demod        : 5
% 2.60/1.37  #Tautology    : 11
% 2.60/1.37  #SimpNegUnit  : 0
% 2.60/1.37  #BackRed      : 0
% 2.60/1.37  
% 2.60/1.37  #Partial instantiations: 0
% 2.60/1.37  #Strategies tried      : 1
% 2.60/1.37  
% 2.60/1.37  Timing (in seconds)
% 2.60/1.37  ----------------------
% 2.60/1.38  Preprocessing        : 0.31
% 2.60/1.38  Parsing              : 0.17
% 2.60/1.38  CNF conversion       : 0.02
% 2.60/1.38  Main loop            : 0.28
% 2.60/1.38  Inferencing          : 0.11
% 2.60/1.38  Reduction            : 0.07
% 2.60/1.38  Demodulation         : 0.05
% 2.60/1.38  BG Simplification    : 0.02
% 2.60/1.38  Subsumption          : 0.06
% 2.60/1.38  Abstraction          : 0.01
% 2.60/1.38  MUC search           : 0.00
% 2.60/1.38  Cooper               : 0.00
% 2.60/1.38  Total                : 0.61
% 2.60/1.38  Index Insertion      : 0.00
% 2.60/1.38  Index Deletion       : 0.00
% 2.60/1.38  Index Matching       : 0.00
% 2.60/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
