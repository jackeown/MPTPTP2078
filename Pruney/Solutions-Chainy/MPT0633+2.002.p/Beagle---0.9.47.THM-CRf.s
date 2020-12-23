%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:19 EST 2020

% Result     : Theorem 1.57s
% Output     : CNFRefutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   24 (  26 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   25 (  29 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_47,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k1_funct_1(k6_relat_1(B),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

tff(c_16,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [A_1] : v1_relat_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4,plain,(
    ! [A_1] : v1_funct_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_2,C_6] :
      ( k1_funct_1(k6_relat_1(A_2),C_6) = C_6
      | ~ r2_hidden(C_6,A_2)
      | ~ v1_funct_1(k6_relat_1(A_2))
      | ~ v1_relat_1(k6_relat_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_20,plain,(
    ! [A_2,C_6] :
      ( k1_funct_1(k6_relat_1(A_2),C_6) = C_6
      | ~ r2_hidden(C_6,A_2)
      | ~ v1_relat_1(k6_relat_1(A_2)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_10])).

tff(c_36,plain,(
    ! [A_10,C_11] :
      ( k1_funct_1(k6_relat_1(A_10),C_11) = C_11
      | ~ r2_hidden(C_11,A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20])).

tff(c_14,plain,(
    k1_funct_1(k6_relat_1('#skF_3'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_42,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_14])).

tff(c_50,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:08:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.57/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.57/1.16  
% 1.57/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.57/1.17  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.57/1.17  
% 1.57/1.17  %Foreground sorts:
% 1.57/1.17  
% 1.57/1.17  
% 1.57/1.17  %Background operators:
% 1.57/1.17  
% 1.57/1.17  
% 1.57/1.17  %Foreground operators:
% 1.57/1.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.57/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.57/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.57/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.57/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.57/1.17  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.57/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.57/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.57/1.17  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.57/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.57/1.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.57/1.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.57/1.17  
% 1.57/1.18  tff(f_47, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k1_funct_1(k6_relat_1(B), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_1)).
% 1.57/1.18  tff(f_29, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.57/1.18  tff(f_42, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 1.57/1.18  tff(c_16, plain, (r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.57/1.18  tff(c_2, plain, (![A_1]: (v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.57/1.18  tff(c_4, plain, (![A_1]: (v1_funct_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.57/1.18  tff(c_10, plain, (![A_2, C_6]: (k1_funct_1(k6_relat_1(A_2), C_6)=C_6 | ~r2_hidden(C_6, A_2) | ~v1_funct_1(k6_relat_1(A_2)) | ~v1_relat_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.57/1.18  tff(c_20, plain, (![A_2, C_6]: (k1_funct_1(k6_relat_1(A_2), C_6)=C_6 | ~r2_hidden(C_6, A_2) | ~v1_relat_1(k6_relat_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_10])).
% 1.57/1.18  tff(c_36, plain, (![A_10, C_11]: (k1_funct_1(k6_relat_1(A_10), C_11)=C_11 | ~r2_hidden(C_11, A_10))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20])).
% 1.57/1.18  tff(c_14, plain, (k1_funct_1(k6_relat_1('#skF_3'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.57/1.18  tff(c_42, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_14])).
% 1.57/1.18  tff(c_50, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_42])).
% 1.57/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.57/1.18  
% 1.57/1.18  Inference rules
% 1.57/1.18  ----------------------
% 1.57/1.18  #Ref     : 0
% 1.57/1.18  #Sup     : 5
% 1.57/1.18  #Fact    : 0
% 1.57/1.18  #Define  : 0
% 1.57/1.18  #Split   : 0
% 1.57/1.18  #Chain   : 0
% 1.57/1.18  #Close   : 0
% 1.57/1.18  
% 1.57/1.18  Ordering : KBO
% 1.57/1.18  
% 1.57/1.18  Simplification rules
% 1.57/1.18  ----------------------
% 1.57/1.18  #Subsume      : 0
% 1.57/1.18  #Demod        : 5
% 1.57/1.18  #Tautology    : 3
% 1.57/1.18  #SimpNegUnit  : 0
% 1.57/1.18  #BackRed      : 0
% 1.57/1.18  
% 1.57/1.18  #Partial instantiations: 0
% 1.57/1.18  #Strategies tried      : 1
% 1.57/1.18  
% 1.57/1.18  Timing (in seconds)
% 1.57/1.18  ----------------------
% 1.57/1.18  Preprocessing        : 0.28
% 1.57/1.18  Parsing              : 0.15
% 1.57/1.18  CNF conversion       : 0.02
% 1.57/1.18  Main loop            : 0.07
% 1.57/1.18  Inferencing          : 0.02
% 1.57/1.18  Reduction            : 0.02
% 1.57/1.18  Demodulation         : 0.02
% 1.57/1.18  BG Simplification    : 0.01
% 1.57/1.18  Subsumption          : 0.01
% 1.57/1.18  Abstraction          : 0.00
% 1.57/1.18  MUC search           : 0.00
% 1.57/1.18  Cooper               : 0.00
% 1.57/1.18  Total                : 0.38
% 1.57/1.18  Index Insertion      : 0.00
% 1.57/1.18  Index Deletion       : 0.00
% 1.57/1.18  Index Matching       : 0.00
% 1.57/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
