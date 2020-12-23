%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:19 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   31 (  35 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   35 (  42 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_55,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k1_funct_1(k6_relat_1(B),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k6_relat_1(A)
      <=> ! [C,D] :
            ( r2_hidden(k4_tarski(C,D),B)
          <=> ( r2_hidden(C,A)
              & C = D ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_32,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_20,plain,(
    ! [A_9] : v1_relat_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_22,plain,(
    ! [A_9] : v1_funct_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_14,plain,(
    ! [D_8,A_1] :
      ( r2_hidden(k4_tarski(D_8,D_8),k6_relat_1(A_1))
      | ~ r2_hidden(D_8,A_1)
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_38,plain,(
    ! [D_8,A_1] :
      ( r2_hidden(k4_tarski(D_8,D_8),k6_relat_1(A_1))
      | ~ r2_hidden(D_8,A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_14])).

tff(c_66,plain,(
    ! [C_28,A_29,B_30] :
      ( k1_funct_1(C_28,A_29) = B_30
      | ~ r2_hidden(k4_tarski(A_29,B_30),C_28)
      | ~ v1_funct_1(C_28)
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_73,plain,(
    ! [A_1,D_8] :
      ( k1_funct_1(k6_relat_1(A_1),D_8) = D_8
      | ~ v1_funct_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1))
      | ~ r2_hidden(D_8,A_1) ) ),
    inference(resolution,[status(thm)],[c_38,c_66])).

tff(c_78,plain,(
    ! [A_31,D_32] :
      ( k1_funct_1(k6_relat_1(A_31),D_32) = D_32
      | ~ r2_hidden(D_32,A_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22,c_73])).

tff(c_30,plain,(
    k1_funct_1(k6_relat_1('#skF_6'),'#skF_5') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_84,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_30])).

tff(c_92,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_84])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n003.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 20:38:12 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.09  
% 1.59/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.10  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 1.59/1.10  
% 1.59/1.10  %Foreground sorts:
% 1.59/1.10  
% 1.59/1.10  
% 1.59/1.10  %Background operators:
% 1.59/1.10  
% 1.59/1.10  
% 1.59/1.10  %Foreground operators:
% 1.59/1.10  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.59/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.59/1.10  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.59/1.10  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.59/1.10  tff('#skF_5', type, '#skF_5': $i).
% 1.59/1.10  tff('#skF_6', type, '#skF_6': $i).
% 1.59/1.10  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.59/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.59/1.10  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.59/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.10  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.59/1.10  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.59/1.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.59/1.10  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.59/1.10  
% 1.74/1.10  tff(f_55, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k1_funct_1(k6_relat_1(B), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_1)).
% 1.74/1.10  tff(f_40, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.74/1.10  tff(f_36, axiom, (![A, B]: (v1_relat_1(B) => ((B = k6_relat_1(A)) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), B) <=> (r2_hidden(C, A) & (C = D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_relat_1)).
% 1.74/1.10  tff(f_50, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 1.74/1.10  tff(c_32, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.74/1.10  tff(c_20, plain, (![A_9]: (v1_relat_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.74/1.10  tff(c_22, plain, (![A_9]: (v1_funct_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.74/1.10  tff(c_14, plain, (![D_8, A_1]: (r2_hidden(k4_tarski(D_8, D_8), k6_relat_1(A_1)) | ~r2_hidden(D_8, A_1) | ~v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.74/1.10  tff(c_38, plain, (![D_8, A_1]: (r2_hidden(k4_tarski(D_8, D_8), k6_relat_1(A_1)) | ~r2_hidden(D_8, A_1))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_14])).
% 1.74/1.10  tff(c_66, plain, (![C_28, A_29, B_30]: (k1_funct_1(C_28, A_29)=B_30 | ~r2_hidden(k4_tarski(A_29, B_30), C_28) | ~v1_funct_1(C_28) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.74/1.10  tff(c_73, plain, (![A_1, D_8]: (k1_funct_1(k6_relat_1(A_1), D_8)=D_8 | ~v1_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)) | ~r2_hidden(D_8, A_1))), inference(resolution, [status(thm)], [c_38, c_66])).
% 1.74/1.10  tff(c_78, plain, (![A_31, D_32]: (k1_funct_1(k6_relat_1(A_31), D_32)=D_32 | ~r2_hidden(D_32, A_31))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22, c_73])).
% 1.74/1.10  tff(c_30, plain, (k1_funct_1(k6_relat_1('#skF_6'), '#skF_5')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.74/1.10  tff(c_84, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_78, c_30])).
% 1.74/1.10  tff(c_92, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_84])).
% 1.74/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.10  
% 1.74/1.10  Inference rules
% 1.74/1.10  ----------------------
% 1.74/1.10  #Ref     : 0
% 1.74/1.10  #Sup     : 9
% 1.74/1.10  #Fact    : 0
% 1.74/1.10  #Define  : 0
% 1.74/1.10  #Split   : 0
% 1.74/1.10  #Chain   : 0
% 1.74/1.10  #Close   : 0
% 1.74/1.10  
% 1.74/1.10  Ordering : KBO
% 1.74/1.10  
% 1.74/1.10  Simplification rules
% 1.74/1.10  ----------------------
% 1.74/1.10  #Subsume      : 0
% 1.74/1.10  #Demod        : 8
% 1.74/1.10  #Tautology    : 3
% 1.74/1.10  #SimpNegUnit  : 0
% 1.74/1.10  #BackRed      : 0
% 1.74/1.10  
% 1.74/1.10  #Partial instantiations: 0
% 1.74/1.10  #Strategies tried      : 1
% 1.74/1.10  
% 1.74/1.10  Timing (in seconds)
% 1.74/1.10  ----------------------
% 1.74/1.11  Preprocessing        : 0.28
% 1.74/1.11  Parsing              : 0.14
% 1.74/1.11  CNF conversion       : 0.02
% 1.74/1.11  Main loop            : 0.09
% 1.74/1.11  Inferencing          : 0.03
% 1.74/1.11  Reduction            : 0.03
% 1.74/1.11  Demodulation         : 0.02
% 1.74/1.11  BG Simplification    : 0.01
% 1.74/1.11  Subsumption          : 0.02
% 1.74/1.11  Abstraction          : 0.01
% 1.74/1.11  MUC search           : 0.00
% 1.74/1.11  Cooper               : 0.00
% 1.74/1.11  Total                : 0.39
% 1.74/1.11  Index Insertion      : 0.00
% 1.74/1.11  Index Deletion       : 0.00
% 1.74/1.11  Index Matching       : 0.00
% 1.74/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
