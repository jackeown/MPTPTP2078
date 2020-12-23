%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:41 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   26 (  30 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    4
%              Number of atoms          :   36 (  56 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r2_hidden > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v5_relat_1(B,A)
          & v1_funct_1(B) )
       => ! [C] :
            ( r2_hidden(C,k1_relat_1(B))
           => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( r2_hidden(C,k2_relat_1(B))
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16,plain,(
    ! [B_11,A_12] :
      ( r2_hidden(k1_funct_1(B_11,A_12),k2_relat_1(B_11))
      | ~ r2_hidden(A_12,k1_relat_1(B_11))
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,k2_relat_1(B_2))
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_20,plain,(
    ! [B_13,A_14,A_15] :
      ( r2_hidden(k1_funct_1(B_13,A_14),A_15)
      | ~ v5_relat_1(B_13,A_15)
      | ~ r2_hidden(A_14,k1_relat_1(B_13))
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(resolution,[status(thm)],[c_16,c_2])).

tff(c_6,plain,(
    ~ r2_hidden(k1_funct_1('#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_26,plain,
    ( ~ v5_relat_1('#skF_2','#skF_1')
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_6])).

tff(c_31,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_10,c_8,c_12,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:03:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.15  
% 1.69/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.16  %$ v5_relat_1 > r2_hidden > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.74/1.16  
% 1.74/1.16  %Foreground sorts:
% 1.74/1.16  
% 1.74/1.16  
% 1.74/1.16  %Background operators:
% 1.74/1.16  
% 1.74/1.16  
% 1.74/1.16  %Foreground operators:
% 1.74/1.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.74/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.74/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.74/1.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.74/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.74/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.74/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.74/1.16  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.74/1.16  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.74/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.74/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.74/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.74/1.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.74/1.16  
% 1.74/1.17  tff(f_54, negated_conjecture, ~(![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 1.74/1.17  tff(f_42, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 1.74/1.17  tff(f_34, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (r2_hidden(C, k2_relat_1(B)) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t202_relat_1)).
% 1.74/1.17  tff(c_14, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.74/1.17  tff(c_10, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.74/1.17  tff(c_8, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.74/1.17  tff(c_12, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.74/1.17  tff(c_16, plain, (![B_11, A_12]: (r2_hidden(k1_funct_1(B_11, A_12), k2_relat_1(B_11)) | ~r2_hidden(A_12, k1_relat_1(B_11)) | ~v1_funct_1(B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.74/1.17  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, k2_relat_1(B_2)) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.74/1.17  tff(c_20, plain, (![B_13, A_14, A_15]: (r2_hidden(k1_funct_1(B_13, A_14), A_15) | ~v5_relat_1(B_13, A_15) | ~r2_hidden(A_14, k1_relat_1(B_13)) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13))), inference(resolution, [status(thm)], [c_16, c_2])).
% 1.74/1.17  tff(c_6, plain, (~r2_hidden(k1_funct_1('#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.74/1.17  tff(c_26, plain, (~v5_relat_1('#skF_2', '#skF_1') | ~r2_hidden('#skF_3', k1_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_20, c_6])).
% 1.74/1.17  tff(c_31, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_10, c_8, c_12, c_26])).
% 1.74/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.17  
% 1.74/1.17  Inference rules
% 1.74/1.17  ----------------------
% 1.74/1.17  #Ref     : 0
% 1.74/1.17  #Sup     : 3
% 1.74/1.17  #Fact    : 0
% 1.74/1.17  #Define  : 0
% 1.74/1.17  #Split   : 0
% 1.74/1.17  #Chain   : 0
% 1.74/1.17  #Close   : 0
% 1.74/1.17  
% 1.74/1.17  Ordering : KBO
% 1.74/1.17  
% 1.74/1.17  Simplification rules
% 1.74/1.17  ----------------------
% 1.74/1.17  #Subsume      : 0
% 1.74/1.17  #Demod        : 4
% 1.74/1.17  #Tautology    : 0
% 1.74/1.17  #SimpNegUnit  : 0
% 1.74/1.17  #BackRed      : 0
% 1.74/1.17  
% 1.74/1.17  #Partial instantiations: 0
% 1.74/1.17  #Strategies tried      : 1
% 1.74/1.17  
% 1.74/1.17  Timing (in seconds)
% 1.74/1.17  ----------------------
% 1.74/1.17  Preprocessing        : 0.27
% 1.74/1.17  Parsing              : 0.15
% 1.74/1.17  CNF conversion       : 0.02
% 1.74/1.17  Main loop            : 0.08
% 1.74/1.17  Inferencing          : 0.03
% 1.74/1.17  Reduction            : 0.02
% 1.74/1.17  Demodulation         : 0.02
% 1.74/1.17  BG Simplification    : 0.01
% 1.74/1.17  Subsumption          : 0.01
% 1.74/1.17  Abstraction          : 0.00
% 1.74/1.17  MUC search           : 0.00
% 1.74/1.17  Cooper               : 0.00
% 1.74/1.17  Total                : 0.37
% 1.74/1.17  Index Insertion      : 0.00
% 1.74/1.17  Index Deletion       : 0.00
% 1.74/1.17  Index Matching       : 0.00
% 1.74/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
