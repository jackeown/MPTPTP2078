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
% DateTime   : Thu Dec  3 10:06:50 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   29 (  35 expanded)
%              Number of leaves         :   14 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   66 (  98 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_wellord1 > r4_wellord1 > v2_wellord1 > v1_relat_1 > v1_funct_1 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(r4_wellord1,type,(
    r4_wellord1: ( $i * $i ) > $o )).

tff(r3_wellord1,type,(
    r3_wellord1: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( ( r4_wellord1(A,B)
                & v2_wellord1(A) )
             => v2_wellord1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_wellord1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
          <=> ? [C] :
                ( v1_relat_1(C)
                & v1_funct_1(C)
                & r3_wellord1(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_wellord1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ( ( v2_wellord1(A)
                  & r3_wellord1(A,B,C) )
               => v2_wellord1(B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_wellord1)).

tff(c_12,plain,(
    ~ v2_wellord1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_14,plain,(
    v2_wellord1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_16,plain,(
    r4_wellord1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6,plain,(
    ! [A_1,B_7] :
      ( v1_funct_1('#skF_1'(A_1,B_7))
      | ~ r4_wellord1(A_1,B_7)
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_1,B_7] :
      ( v1_relat_1('#skF_1'(A_1,B_7))
      | ~ r4_wellord1(A_1,B_7)
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_1,B_7] :
      ( r3_wellord1(A_1,B_7,'#skF_1'(A_1,B_7))
      | ~ r4_wellord1(A_1,B_7)
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_29,plain,(
    ! [B_28,A_29,C_30] :
      ( v2_wellord1(B_28)
      | ~ r3_wellord1(A_29,B_28,C_30)
      | ~ v2_wellord1(A_29)
      | ~ v1_funct_1(C_30)
      | ~ v1_relat_1(C_30)
      | ~ v1_relat_1(B_28)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_34,plain,(
    ! [B_31,A_32] :
      ( v2_wellord1(B_31)
      | ~ v2_wellord1(A_32)
      | ~ v1_funct_1('#skF_1'(A_32,B_31))
      | ~ v1_relat_1('#skF_1'(A_32,B_31))
      | ~ r4_wellord1(A_32,B_31)
      | ~ v1_relat_1(B_31)
      | ~ v1_relat_1(A_32) ) ),
    inference(resolution,[status(thm)],[c_4,c_29])).

tff(c_39,plain,(
    ! [B_33,A_34] :
      ( v2_wellord1(B_33)
      | ~ v2_wellord1(A_34)
      | ~ v1_funct_1('#skF_1'(A_34,B_33))
      | ~ r4_wellord1(A_34,B_33)
      | ~ v1_relat_1(B_33)
      | ~ v1_relat_1(A_34) ) ),
    inference(resolution,[status(thm)],[c_8,c_34])).

tff(c_44,plain,(
    ! [B_35,A_36] :
      ( v2_wellord1(B_35)
      | ~ v2_wellord1(A_36)
      | ~ r4_wellord1(A_36,B_35)
      | ~ v1_relat_1(B_35)
      | ~ v1_relat_1(A_36) ) ),
    inference(resolution,[status(thm)],[c_6,c_39])).

tff(c_47,plain,
    ( v2_wellord1('#skF_3')
    | ~ v2_wellord1('#skF_2')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_44])).

tff(c_50,plain,(
    v2_wellord1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_14,c_47])).

tff(c_52,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:45:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.19  
% 1.80/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.19  %$ r3_wellord1 > r4_wellord1 > v2_wellord1 > v1_relat_1 > v1_funct_1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.80/1.19  
% 1.80/1.19  %Foreground sorts:
% 1.80/1.19  
% 1.80/1.19  
% 1.80/1.19  %Background operators:
% 1.80/1.19  
% 1.80/1.19  
% 1.80/1.19  %Foreground operators:
% 1.80/1.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.80/1.19  tff(r4_wellord1, type, r4_wellord1: ($i * $i) > $o).
% 1.80/1.19  tff(r3_wellord1, type, r3_wellord1: ($i * $i * $i) > $o).
% 1.80/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.19  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 1.80/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.80/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.80/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.80/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.19  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.80/1.19  
% 1.80/1.20  tff(f_67, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => ((r4_wellord1(A, B) & v2_wellord1(A)) => v2_wellord1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_wellord1)).
% 1.80/1.20  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r4_wellord1(A, B) <=> (?[C]: ((v1_relat_1(C) & v1_funct_1(C)) & r3_wellord1(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_wellord1)).
% 1.80/1.20  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((v2_wellord1(A) & r3_wellord1(A, B, C)) => v2_wellord1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_wellord1)).
% 1.80/1.20  tff(c_12, plain, (~v2_wellord1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.80/1.20  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.80/1.20  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.80/1.20  tff(c_14, plain, (v2_wellord1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.80/1.20  tff(c_16, plain, (r4_wellord1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.80/1.20  tff(c_6, plain, (![A_1, B_7]: (v1_funct_1('#skF_1'(A_1, B_7)) | ~r4_wellord1(A_1, B_7) | ~v1_relat_1(B_7) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.80/1.20  tff(c_8, plain, (![A_1, B_7]: (v1_relat_1('#skF_1'(A_1, B_7)) | ~r4_wellord1(A_1, B_7) | ~v1_relat_1(B_7) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.80/1.20  tff(c_4, plain, (![A_1, B_7]: (r3_wellord1(A_1, B_7, '#skF_1'(A_1, B_7)) | ~r4_wellord1(A_1, B_7) | ~v1_relat_1(B_7) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.80/1.20  tff(c_29, plain, (![B_28, A_29, C_30]: (v2_wellord1(B_28) | ~r3_wellord1(A_29, B_28, C_30) | ~v2_wellord1(A_29) | ~v1_funct_1(C_30) | ~v1_relat_1(C_30) | ~v1_relat_1(B_28) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.80/1.20  tff(c_34, plain, (![B_31, A_32]: (v2_wellord1(B_31) | ~v2_wellord1(A_32) | ~v1_funct_1('#skF_1'(A_32, B_31)) | ~v1_relat_1('#skF_1'(A_32, B_31)) | ~r4_wellord1(A_32, B_31) | ~v1_relat_1(B_31) | ~v1_relat_1(A_32))), inference(resolution, [status(thm)], [c_4, c_29])).
% 1.80/1.20  tff(c_39, plain, (![B_33, A_34]: (v2_wellord1(B_33) | ~v2_wellord1(A_34) | ~v1_funct_1('#skF_1'(A_34, B_33)) | ~r4_wellord1(A_34, B_33) | ~v1_relat_1(B_33) | ~v1_relat_1(A_34))), inference(resolution, [status(thm)], [c_8, c_34])).
% 1.80/1.20  tff(c_44, plain, (![B_35, A_36]: (v2_wellord1(B_35) | ~v2_wellord1(A_36) | ~r4_wellord1(A_36, B_35) | ~v1_relat_1(B_35) | ~v1_relat_1(A_36))), inference(resolution, [status(thm)], [c_6, c_39])).
% 1.80/1.20  tff(c_47, plain, (v2_wellord1('#skF_3') | ~v2_wellord1('#skF_2') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_44])).
% 1.80/1.20  tff(c_50, plain, (v2_wellord1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_14, c_47])).
% 1.80/1.20  tff(c_52, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_50])).
% 1.80/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.20  
% 1.80/1.20  Inference rules
% 1.80/1.20  ----------------------
% 1.80/1.20  #Ref     : 0
% 1.80/1.20  #Sup     : 5
% 1.80/1.20  #Fact    : 0
% 1.80/1.20  #Define  : 0
% 1.80/1.20  #Split   : 0
% 1.80/1.20  #Chain   : 0
% 1.80/1.20  #Close   : 0
% 1.80/1.20  
% 1.80/1.20  Ordering : KBO
% 1.80/1.20  
% 1.80/1.20  Simplification rules
% 1.80/1.20  ----------------------
% 1.80/1.20  #Subsume      : 2
% 1.80/1.20  #Demod        : 3
% 1.80/1.20  #Tautology    : 1
% 1.80/1.20  #SimpNegUnit  : 1
% 1.80/1.20  #BackRed      : 0
% 1.80/1.20  
% 1.80/1.20  #Partial instantiations: 0
% 1.80/1.20  #Strategies tried      : 1
% 1.80/1.20  
% 1.80/1.20  Timing (in seconds)
% 1.80/1.20  ----------------------
% 1.80/1.21  Preprocessing        : 0.25
% 1.80/1.21  Parsing              : 0.13
% 1.80/1.21  CNF conversion       : 0.02
% 1.80/1.21  Main loop            : 0.15
% 1.80/1.21  Inferencing          : 0.08
% 1.80/1.21  Reduction            : 0.03
% 1.80/1.21  Demodulation         : 0.02
% 1.80/1.21  BG Simplification    : 0.01
% 1.80/1.21  Subsumption          : 0.02
% 1.80/1.21  Abstraction          : 0.00
% 1.80/1.21  MUC search           : 0.00
% 1.80/1.21  Cooper               : 0.00
% 1.80/1.21  Total                : 0.43
% 1.80/1.21  Index Insertion      : 0.00
% 1.80/1.21  Index Deletion       : 0.00
% 1.80/1.21  Index Matching       : 0.00
% 1.80/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
