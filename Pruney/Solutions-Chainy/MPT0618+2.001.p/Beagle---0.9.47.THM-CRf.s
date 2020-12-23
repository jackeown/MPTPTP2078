%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:51 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   25 (  28 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    4
%              Number of atoms          :   35 (  47 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r2_hidden(A,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_51,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_16,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_34,plain,(
    ! [B_17,A_18] :
      ( r2_hidden(k4_tarski(B_17,k1_funct_1(A_18,B_17)),A_18)
      | ~ r2_hidden(B_17,k1_relat_1(A_18))
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [B_2,C_3,A_1] :
      ( r2_hidden(B_2,k2_relat_1(C_3))
      | ~ r2_hidden(k4_tarski(A_1,B_2),C_3)
      | ~ v1_relat_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_43,plain,(
    ! [A_19,B_20] :
      ( r2_hidden(k1_funct_1(A_19,B_20),k2_relat_1(A_19))
      | ~ r2_hidden(B_20,k1_relat_1(A_19))
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(resolution,[status(thm)],[c_34,c_2])).

tff(c_14,plain,(
    ~ r2_hidden(k1_funct_1('#skF_2','#skF_1'),k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_46,plain,
    ( ~ r2_hidden('#skF_1',k1_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_43,c_14])).

tff(c_50,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:49:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.13  
% 1.61/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.13  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.61/1.13  
% 1.61/1.13  %Foreground sorts:
% 1.61/1.13  
% 1.61/1.13  
% 1.61/1.13  %Background operators:
% 1.61/1.13  
% 1.61/1.13  
% 1.61/1.13  %Foreground operators:
% 1.61/1.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.61/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.61/1.13  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.61/1.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.61/1.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.61/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.61/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.61/1.13  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.61/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.61/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.61/1.13  
% 1.61/1.14  tff(f_60, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 1.61/1.14  tff(f_51, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 1.61/1.14  tff(f_33, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 1.61/1.14  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.61/1.14  tff(c_18, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.61/1.14  tff(c_16, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.61/1.14  tff(c_34, plain, (![B_17, A_18]: (r2_hidden(k4_tarski(B_17, k1_funct_1(A_18, B_17)), A_18) | ~r2_hidden(B_17, k1_relat_1(A_18)) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.61/1.14  tff(c_2, plain, (![B_2, C_3, A_1]: (r2_hidden(B_2, k2_relat_1(C_3)) | ~r2_hidden(k4_tarski(A_1, B_2), C_3) | ~v1_relat_1(C_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.61/1.14  tff(c_43, plain, (![A_19, B_20]: (r2_hidden(k1_funct_1(A_19, B_20), k2_relat_1(A_19)) | ~r2_hidden(B_20, k1_relat_1(A_19)) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(resolution, [status(thm)], [c_34, c_2])).
% 1.61/1.14  tff(c_14, plain, (~r2_hidden(k1_funct_1('#skF_2', '#skF_1'), k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.61/1.14  tff(c_46, plain, (~r2_hidden('#skF_1', k1_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_43, c_14])).
% 1.61/1.14  tff(c_50, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_16, c_46])).
% 1.61/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.14  
% 1.61/1.14  Inference rules
% 1.61/1.14  ----------------------
% 1.61/1.14  #Ref     : 0
% 1.61/1.14  #Sup     : 5
% 1.61/1.14  #Fact    : 0
% 1.61/1.14  #Define  : 0
% 1.61/1.14  #Split   : 0
% 1.61/1.14  #Chain   : 0
% 1.61/1.14  #Close   : 0
% 1.61/1.14  
% 1.61/1.14  Ordering : KBO
% 1.61/1.14  
% 1.61/1.14  Simplification rules
% 1.61/1.14  ----------------------
% 1.61/1.14  #Subsume      : 1
% 1.61/1.14  #Demod        : 3
% 1.61/1.14  #Tautology    : 1
% 1.61/1.14  #SimpNegUnit  : 0
% 1.61/1.14  #BackRed      : 0
% 1.61/1.14  
% 1.61/1.14  #Partial instantiations: 0
% 1.61/1.14  #Strategies tried      : 1
% 1.61/1.14  
% 1.61/1.14  Timing (in seconds)
% 1.61/1.14  ----------------------
% 1.61/1.14  Preprocessing        : 0.28
% 1.61/1.14  Parsing              : 0.15
% 1.61/1.14  CNF conversion       : 0.02
% 1.61/1.14  Main loop            : 0.10
% 1.61/1.14  Inferencing          : 0.05
% 1.61/1.14  Reduction            : 0.02
% 1.61/1.14  Demodulation         : 0.02
% 1.61/1.14  BG Simplification    : 0.01
% 1.61/1.14  Subsumption          : 0.02
% 1.61/1.14  Abstraction          : 0.00
% 1.61/1.14  MUC search           : 0.00
% 1.61/1.14  Cooper               : 0.00
% 1.61/1.14  Total                : 0.41
% 1.61/1.14  Index Insertion      : 0.00
% 1.61/1.14  Index Deletion       : 0.00
% 1.61/1.14  Index Matching       : 0.00
% 1.61/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
