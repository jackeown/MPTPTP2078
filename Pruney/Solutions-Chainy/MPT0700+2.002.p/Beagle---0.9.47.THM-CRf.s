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
% DateTime   : Thu Dec  3 10:05:01 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   31 (  35 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   68 (  84 expanded)
%              Number of equality atoms :   10 (  13 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k2_funct_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( v2_funct_1(B)
         => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_49,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_16,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_14,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_funct_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_relat_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_4] :
      ( v2_funct_1(k2_funct_1(A_4))
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [A_5] :
      ( k2_funct_1(k2_funct_1(A_5)) = A_5
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_48,plain,(
    ! [B_10,A_11] :
      ( k10_relat_1(k2_funct_1(B_10),A_11) = k9_relat_1(B_10,A_11)
      | ~ v2_funct_1(B_10)
      | ~ v1_funct_1(B_10)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_60,plain,(
    ! [A_12,A_13] :
      ( k9_relat_1(k2_funct_1(A_12),A_13) = k10_relat_1(A_12,A_13)
      | ~ v2_funct_1(k2_funct_1(A_12))
      | ~ v1_funct_1(k2_funct_1(A_12))
      | ~ v1_relat_1(k2_funct_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_48])).

tff(c_66,plain,(
    ! [A_14,A_15] :
      ( k9_relat_1(k2_funct_1(A_14),A_15) = k10_relat_1(A_14,A_15)
      | ~ v1_funct_1(k2_funct_1(A_14))
      | ~ v1_relat_1(k2_funct_1(A_14))
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(resolution,[status(thm)],[c_8,c_60])).

tff(c_72,plain,(
    ! [A_16,A_17] :
      ( k9_relat_1(k2_funct_1(A_16),A_17) = k10_relat_1(A_16,A_17)
      | ~ v1_funct_1(k2_funct_1(A_16))
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(resolution,[status(thm)],[c_4,c_66])).

tff(c_78,plain,(
    ! [A_18,A_19] :
      ( k9_relat_1(k2_funct_1(A_18),A_19) = k10_relat_1(A_18,A_19)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(resolution,[status(thm)],[c_2,c_72])).

tff(c_12,plain,(
    k9_relat_1(k2_funct_1('#skF_2'),'#skF_1') != k10_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_84,plain,
    ( ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_12])).

tff(c_95,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_14,c_84])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:47:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.14  
% 1.80/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.15  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k2_funct_1 > #skF_2 > #skF_1
% 1.80/1.15  
% 1.80/1.15  %Foreground sorts:
% 1.80/1.15  
% 1.80/1.15  
% 1.80/1.15  %Background operators:
% 1.80/1.15  
% 1.80/1.15  
% 1.80/1.15  %Foreground operators:
% 1.80/1.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.80/1.15  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 1.80/1.15  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.80/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.80/1.15  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.80/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.80/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.15  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.80/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.80/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.15  
% 1.80/1.16  tff(f_66, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 1.80/1.16  tff(f_33, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 1.80/1.16  tff(f_49, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_1)).
% 1.80/1.16  tff(f_57, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 1.80/1.16  tff(f_41, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_funct_1)).
% 1.80/1.16  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.80/1.16  tff(c_16, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.80/1.16  tff(c_14, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.80/1.16  tff(c_2, plain, (![A_1]: (v1_funct_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.80/1.16  tff(c_4, plain, (![A_1]: (v1_relat_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.80/1.16  tff(c_8, plain, (![A_4]: (v2_funct_1(k2_funct_1(A_4)) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.80/1.16  tff(c_10, plain, (![A_5]: (k2_funct_1(k2_funct_1(A_5))=A_5 | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.80/1.16  tff(c_48, plain, (![B_10, A_11]: (k10_relat_1(k2_funct_1(B_10), A_11)=k9_relat_1(B_10, A_11) | ~v2_funct_1(B_10) | ~v1_funct_1(B_10) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.80/1.16  tff(c_60, plain, (![A_12, A_13]: (k9_relat_1(k2_funct_1(A_12), A_13)=k10_relat_1(A_12, A_13) | ~v2_funct_1(k2_funct_1(A_12)) | ~v1_funct_1(k2_funct_1(A_12)) | ~v1_relat_1(k2_funct_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(superposition, [status(thm), theory('equality')], [c_10, c_48])).
% 1.80/1.16  tff(c_66, plain, (![A_14, A_15]: (k9_relat_1(k2_funct_1(A_14), A_15)=k10_relat_1(A_14, A_15) | ~v1_funct_1(k2_funct_1(A_14)) | ~v1_relat_1(k2_funct_1(A_14)) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(resolution, [status(thm)], [c_8, c_60])).
% 1.80/1.16  tff(c_72, plain, (![A_16, A_17]: (k9_relat_1(k2_funct_1(A_16), A_17)=k10_relat_1(A_16, A_17) | ~v1_funct_1(k2_funct_1(A_16)) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(resolution, [status(thm)], [c_4, c_66])).
% 1.80/1.16  tff(c_78, plain, (![A_18, A_19]: (k9_relat_1(k2_funct_1(A_18), A_19)=k10_relat_1(A_18, A_19) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(resolution, [status(thm)], [c_2, c_72])).
% 1.80/1.16  tff(c_12, plain, (k9_relat_1(k2_funct_1('#skF_2'), '#skF_1')!=k10_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.80/1.16  tff(c_84, plain, (~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_78, c_12])).
% 1.80/1.16  tff(c_95, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_14, c_84])).
% 1.80/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.16  
% 1.80/1.16  Inference rules
% 1.80/1.16  ----------------------
% 1.80/1.16  #Ref     : 0
% 1.80/1.16  #Sup     : 20
% 1.80/1.16  #Fact    : 0
% 1.80/1.16  #Define  : 0
% 1.80/1.16  #Split   : 0
% 1.80/1.16  #Chain   : 0
% 1.80/1.16  #Close   : 0
% 1.80/1.16  
% 1.80/1.16  Ordering : KBO
% 1.80/1.16  
% 1.80/1.16  Simplification rules
% 1.80/1.16  ----------------------
% 1.80/1.16  #Subsume      : 3
% 1.80/1.16  #Demod        : 3
% 1.80/1.16  #Tautology    : 10
% 1.80/1.16  #SimpNegUnit  : 0
% 1.80/1.16  #BackRed      : 0
% 1.80/1.16  
% 1.80/1.16  #Partial instantiations: 0
% 1.80/1.16  #Strategies tried      : 1
% 1.80/1.16  
% 1.80/1.16  Timing (in seconds)
% 1.80/1.16  ----------------------
% 1.80/1.16  Preprocessing        : 0.26
% 1.80/1.16  Parsing              : 0.14
% 1.80/1.16  CNF conversion       : 0.02
% 1.80/1.16  Main loop            : 0.14
% 1.80/1.16  Inferencing          : 0.06
% 1.80/1.16  Reduction            : 0.03
% 1.80/1.16  Demodulation         : 0.03
% 1.80/1.16  BG Simplification    : 0.01
% 1.80/1.16  Subsumption          : 0.03
% 1.80/1.16  Abstraction          : 0.01
% 1.80/1.16  MUC search           : 0.00
% 1.80/1.16  Cooper               : 0.00
% 1.80/1.16  Total                : 0.42
% 1.80/1.16  Index Insertion      : 0.00
% 1.80/1.16  Index Deletion       : 0.00
% 1.80/1.16  Index Matching       : 0.00
% 1.80/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
