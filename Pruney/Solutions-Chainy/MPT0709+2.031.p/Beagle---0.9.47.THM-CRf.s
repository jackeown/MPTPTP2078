%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:28 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   31 (  36 expanded)
%              Number of leaves         :   16 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   55 (  78 expanded)
%              Number of equality atoms :    8 (  13 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( r1_tarski(A,k1_relat_1(B))
            & v2_funct_1(B) )
         => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

tff(c_12,plain,(
    k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_16,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    ! [A_13,C_14,B_15] :
      ( r1_tarski(A_13,k10_relat_1(C_14,B_15))
      | ~ r1_tarski(k9_relat_1(C_14,A_13),B_15)
      | ~ r1_tarski(A_13,k1_relat_1(C_14))
      | ~ v1_funct_1(C_14)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_43,plain,(
    ! [A_13,C_14] :
      ( r1_tarski(A_13,k10_relat_1(C_14,k9_relat_1(C_14,A_13)))
      | ~ r1_tarski(A_13,k1_relat_1(C_14))
      | ~ v1_funct_1(C_14)
      | ~ v1_relat_1(C_14) ) ),
    inference(resolution,[status(thm)],[c_6,c_38])).

tff(c_34,plain,(
    ! [B_11,A_12] :
      ( r1_tarski(k10_relat_1(B_11,k9_relat_1(B_11,A_12)),A_12)
      | ~ v2_funct_1(B_11)
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_53,plain,(
    ! [B_18,A_19] :
      ( k10_relat_1(B_18,k9_relat_1(B_18,A_19)) = A_19
      | ~ r1_tarski(A_19,k10_relat_1(B_18,k9_relat_1(B_18,A_19)))
      | ~ v2_funct_1(B_18)
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(resolution,[status(thm)],[c_34,c_2])).

tff(c_58,plain,(
    ! [C_20,A_21] :
      ( k10_relat_1(C_20,k9_relat_1(C_20,A_21)) = A_21
      | ~ v2_funct_1(C_20)
      | ~ r1_tarski(A_21,k1_relat_1(C_20))
      | ~ v1_funct_1(C_20)
      | ~ v1_relat_1(C_20) ) ),
    inference(resolution,[status(thm)],[c_43,c_53])).

tff(c_63,plain,
    ( k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_58])).

tff(c_70,plain,(
    k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_14,c_63])).

tff(c_72,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_70])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:47:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.14  
% 1.73/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.14  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_1
% 1.73/1.14  
% 1.73/1.14  %Foreground sorts:
% 1.73/1.14  
% 1.73/1.14  
% 1.73/1.14  %Background operators:
% 1.73/1.14  
% 1.73/1.14  
% 1.73/1.14  %Foreground operators:
% 1.73/1.14  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.73/1.14  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.73/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.73/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.73/1.14  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.73/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.73/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.14  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.73/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.73/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.73/1.14  
% 1.73/1.15  tff(f_60, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 1.73/1.15  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.73/1.15  tff(f_49, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 1.73/1.15  tff(f_39, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_funct_1)).
% 1.73/1.15  tff(c_12, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.73/1.15  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.73/1.15  tff(c_18, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.73/1.15  tff(c_14, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.73/1.15  tff(c_16, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.73/1.15  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.73/1.15  tff(c_38, plain, (![A_13, C_14, B_15]: (r1_tarski(A_13, k10_relat_1(C_14, B_15)) | ~r1_tarski(k9_relat_1(C_14, A_13), B_15) | ~r1_tarski(A_13, k1_relat_1(C_14)) | ~v1_funct_1(C_14) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.73/1.15  tff(c_43, plain, (![A_13, C_14]: (r1_tarski(A_13, k10_relat_1(C_14, k9_relat_1(C_14, A_13))) | ~r1_tarski(A_13, k1_relat_1(C_14)) | ~v1_funct_1(C_14) | ~v1_relat_1(C_14))), inference(resolution, [status(thm)], [c_6, c_38])).
% 1.73/1.15  tff(c_34, plain, (![B_11, A_12]: (r1_tarski(k10_relat_1(B_11, k9_relat_1(B_11, A_12)), A_12) | ~v2_funct_1(B_11) | ~v1_funct_1(B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.73/1.15  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.73/1.15  tff(c_53, plain, (![B_18, A_19]: (k10_relat_1(B_18, k9_relat_1(B_18, A_19))=A_19 | ~r1_tarski(A_19, k10_relat_1(B_18, k9_relat_1(B_18, A_19))) | ~v2_funct_1(B_18) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18))), inference(resolution, [status(thm)], [c_34, c_2])).
% 1.73/1.15  tff(c_58, plain, (![C_20, A_21]: (k10_relat_1(C_20, k9_relat_1(C_20, A_21))=A_21 | ~v2_funct_1(C_20) | ~r1_tarski(A_21, k1_relat_1(C_20)) | ~v1_funct_1(C_20) | ~v1_relat_1(C_20))), inference(resolution, [status(thm)], [c_43, c_53])).
% 1.73/1.15  tff(c_63, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_58])).
% 1.73/1.15  tff(c_70, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_14, c_63])).
% 1.73/1.15  tff(c_72, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_70])).
% 1.73/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.15  
% 1.73/1.15  Inference rules
% 1.73/1.15  ----------------------
% 1.73/1.15  #Ref     : 0
% 1.73/1.15  #Sup     : 10
% 1.73/1.15  #Fact    : 0
% 1.73/1.15  #Define  : 0
% 1.73/1.15  #Split   : 1
% 1.73/1.15  #Chain   : 0
% 1.73/1.15  #Close   : 0
% 1.73/1.15  
% 1.73/1.15  Ordering : KBO
% 1.73/1.15  
% 1.73/1.15  Simplification rules
% 1.73/1.15  ----------------------
% 1.73/1.15  #Subsume      : 0
% 1.73/1.15  #Demod        : 5
% 1.73/1.15  #Tautology    : 2
% 1.73/1.15  #SimpNegUnit  : 1
% 1.73/1.15  #BackRed      : 0
% 1.73/1.15  
% 1.73/1.15  #Partial instantiations: 0
% 1.73/1.15  #Strategies tried      : 1
% 1.73/1.15  
% 1.73/1.15  Timing (in seconds)
% 1.73/1.15  ----------------------
% 1.73/1.16  Preprocessing        : 0.26
% 1.73/1.16  Parsing              : 0.15
% 1.73/1.16  CNF conversion       : 0.01
% 1.73/1.16  Main loop            : 0.12
% 1.73/1.16  Inferencing          : 0.05
% 1.73/1.16  Reduction            : 0.03
% 1.73/1.16  Demodulation         : 0.02
% 1.73/1.16  BG Simplification    : 0.01
% 1.73/1.16  Subsumption          : 0.03
% 1.73/1.16  Abstraction          : 0.01
% 1.73/1.16  MUC search           : 0.00
% 1.73/1.16  Cooper               : 0.00
% 1.73/1.16  Total                : 0.41
% 1.73/1.16  Index Insertion      : 0.00
% 1.73/1.16  Index Deletion       : 0.00
% 1.73/1.16  Index Matching       : 0.00
% 1.73/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
