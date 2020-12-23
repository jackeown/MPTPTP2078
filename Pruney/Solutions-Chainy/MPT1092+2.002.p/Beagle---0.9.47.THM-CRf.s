%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:25 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   22 (  25 expanded)
%              Number of leaves         :   13 (  16 expanded)
%              Depth                    :    4
%              Number of atoms          :   29 (  41 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > v1_funct_1 > v1_finset_1 > k9_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_46,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_finset_1(k1_relat_1(A))
         => v1_finset_1(k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_finset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_finset_1(A)
       => v1_finset_1(k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_finset_1)).

tff(c_12,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8,plain,(
    v1_finset_1(k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [A_1] :
      ( k9_relat_1(A_1,k1_relat_1(A_1)) = k2_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    ! [B_5,A_6] :
      ( v1_finset_1(k9_relat_1(B_5,A_6))
      | ~ v1_finset_1(A_6)
      | ~ v1_funct_1(B_5)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_26,plain,(
    ! [A_7] :
      ( v1_finset_1(k2_relat_1(A_7))
      | ~ v1_finset_1(k1_relat_1(A_7))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_22])).

tff(c_6,plain,(
    ~ v1_finset_1(k2_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_29,plain,
    ( ~ v1_finset_1(k1_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_6])).

tff(c_33,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10,c_8,c_29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:37:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.42  
% 1.81/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.43  %$ v1_relat_1 > v1_funct_1 > v1_finset_1 > k9_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1
% 1.81/1.43  
% 1.81/1.43  %Foreground sorts:
% 1.81/1.43  
% 1.81/1.43  
% 1.81/1.43  %Background operators:
% 1.81/1.43  
% 1.81/1.43  
% 1.81/1.43  %Foreground operators:
% 1.81/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.81/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.81/1.43  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.81/1.43  tff('#skF_1', type, '#skF_1': $i).
% 1.81/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.81/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.43  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 1.81/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.81/1.43  
% 1.81/1.44  tff(f_46, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_finset_1(k1_relat_1(A)) => v1_finset_1(k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_finset_1)).
% 1.81/1.44  tff(f_29, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 1.81/1.44  tff(f_37, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v1_finset_1(A) => v1_finset_1(k9_relat_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_finset_1)).
% 1.81/1.44  tff(c_12, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.81/1.44  tff(c_10, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.81/1.44  tff(c_8, plain, (v1_finset_1(k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.81/1.44  tff(c_2, plain, (![A_1]: (k9_relat_1(A_1, k1_relat_1(A_1))=k2_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.81/1.44  tff(c_22, plain, (![B_5, A_6]: (v1_finset_1(k9_relat_1(B_5, A_6)) | ~v1_finset_1(A_6) | ~v1_funct_1(B_5) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.81/1.44  tff(c_26, plain, (![A_7]: (v1_finset_1(k2_relat_1(A_7)) | ~v1_finset_1(k1_relat_1(A_7)) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7) | ~v1_relat_1(A_7))), inference(superposition, [status(thm), theory('equality')], [c_2, c_22])).
% 1.81/1.44  tff(c_6, plain, (~v1_finset_1(k2_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.81/1.44  tff(c_29, plain, (~v1_finset_1(k1_relat_1('#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_6])).
% 1.81/1.44  tff(c_33, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_10, c_8, c_29])).
% 1.81/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.44  
% 1.81/1.44  Inference rules
% 1.81/1.44  ----------------------
% 1.81/1.44  #Ref     : 0
% 1.81/1.44  #Sup     : 4
% 1.81/1.44  #Fact    : 0
% 1.81/1.44  #Define  : 0
% 1.81/1.44  #Split   : 0
% 1.81/1.44  #Chain   : 0
% 1.81/1.44  #Close   : 0
% 1.81/1.44  
% 1.81/1.44  Ordering : KBO
% 1.81/1.44  
% 1.81/1.44  Simplification rules
% 1.81/1.44  ----------------------
% 1.81/1.44  #Subsume      : 0
% 1.81/1.44  #Demod        : 3
% 1.81/1.44  #Tautology    : 2
% 1.81/1.44  #SimpNegUnit  : 0
% 1.81/1.44  #BackRed      : 0
% 1.81/1.44  
% 1.81/1.44  #Partial instantiations: 0
% 1.81/1.44  #Strategies tried      : 1
% 1.81/1.44  
% 1.81/1.44  Timing (in seconds)
% 1.81/1.44  ----------------------
% 1.81/1.44  Preprocessing        : 0.38
% 1.81/1.44  Parsing              : 0.21
% 1.81/1.44  CNF conversion       : 0.02
% 1.81/1.44  Main loop            : 0.13
% 1.81/1.44  Inferencing          : 0.07
% 1.81/1.44  Reduction            : 0.03
% 1.81/1.44  Demodulation         : 0.03
% 1.81/1.44  BG Simplification    : 0.01
% 1.81/1.44  Subsumption          : 0.01
% 1.81/1.44  Abstraction          : 0.00
% 1.81/1.44  MUC search           : 0.00
% 1.81/1.44  Cooper               : 0.00
% 1.81/1.44  Total                : 0.55
% 1.81/1.44  Index Insertion      : 0.00
% 1.81/1.45  Index Deletion       : 0.00
% 1.81/1.45  Index Matching       : 0.00
% 1.81/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
