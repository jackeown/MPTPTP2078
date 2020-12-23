%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:34 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   34 (  44 expanded)
%              Number of leaves         :   17 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   44 ( 102 expanded)
%              Number of equality atoms :   18 (  42 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( v1_relat_1(C)
           => ! [D] :
                ( v1_relat_1(D)
               => ( ( r1_tarski(k2_relat_1(B),A)
                    & k5_relat_1(B,C) = k6_relat_1(k1_relat_1(D))
                    & k5_relat_1(C,D) = k6_relat_1(A) )
                 => D = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(c_8,plain,(
    '#skF_2' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_16,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_14,plain,(
    r1_tarski(k2_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_47,plain,(
    ! [B_16,A_17] :
      ( k5_relat_1(B_16,k6_relat_1(A_17)) = B_16
      | ~ r1_tarski(k2_relat_1(B_16),A_17)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_50,plain,
    ( k5_relat_1('#skF_2',k6_relat_1('#skF_1')) = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_47])).

tff(c_53,plain,(
    k5_relat_1('#skF_2',k6_relat_1('#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_50])).

tff(c_10,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_58,plain,(
    ! [A_18,B_19,C_20] :
      ( k5_relat_1(k5_relat_1(A_18,B_19),C_20) = k5_relat_1(A_18,k5_relat_1(B_19,C_20))
      | ~ v1_relat_1(C_20)
      | ~ v1_relat_1(B_19)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    k6_relat_1(k1_relat_1('#skF_4')) = k5_relat_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_29,plain,(
    ! [A_15] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_15)),A_15) = A_15
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_38,plain,
    ( k5_relat_1(k5_relat_1('#skF_2','#skF_3'),'#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_29])).

tff(c_42,plain,(
    k5_relat_1(k5_relat_1('#skF_2','#skF_3'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_38])).

tff(c_67,plain,
    ( k5_relat_1('#skF_2',k5_relat_1('#skF_3','#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_42])).

tff(c_91,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_53,c_10,c_67])).

tff(c_93,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_91])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:55:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.10  
% 1.67/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.10  %$ r1_tarski > v1_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.67/1.10  
% 1.67/1.10  %Foreground sorts:
% 1.67/1.10  
% 1.67/1.10  
% 1.67/1.10  %Background operators:
% 1.67/1.10  
% 1.67/1.10  
% 1.67/1.10  %Foreground operators:
% 1.67/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.10  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.67/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.67/1.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.67/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.10  tff('#skF_3', type, '#skF_3': $i).
% 1.67/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.67/1.10  tff('#skF_4', type, '#skF_4': $i).
% 1.67/1.10  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.67/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.67/1.10  
% 1.67/1.11  tff(f_62, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => (((r1_tarski(k2_relat_1(B), A) & (k5_relat_1(B, C) = k6_relat_1(k1_relat_1(D)))) & (k5_relat_1(C, D) = k6_relat_1(A))) => (D = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_relat_1)).
% 1.67/1.11  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 1.67/1.11  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 1.67/1.11  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 1.67/1.11  tff(c_8, plain, ('#skF_2'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.67/1.11  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.67/1.11  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.67/1.11  tff(c_16, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.67/1.11  tff(c_14, plain, (r1_tarski(k2_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.67/1.11  tff(c_47, plain, (![B_16, A_17]: (k5_relat_1(B_16, k6_relat_1(A_17))=B_16 | ~r1_tarski(k2_relat_1(B_16), A_17) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.67/1.11  tff(c_50, plain, (k5_relat_1('#skF_2', k6_relat_1('#skF_1'))='#skF_2' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_14, c_47])).
% 1.67/1.11  tff(c_53, plain, (k5_relat_1('#skF_2', k6_relat_1('#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_50])).
% 1.67/1.11  tff(c_10, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.67/1.11  tff(c_58, plain, (![A_18, B_19, C_20]: (k5_relat_1(k5_relat_1(A_18, B_19), C_20)=k5_relat_1(A_18, k5_relat_1(B_19, C_20)) | ~v1_relat_1(C_20) | ~v1_relat_1(B_19) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.67/1.11  tff(c_12, plain, (k6_relat_1(k1_relat_1('#skF_4'))=k5_relat_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.67/1.11  tff(c_29, plain, (![A_15]: (k5_relat_1(k6_relat_1(k1_relat_1(A_15)), A_15)=A_15 | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.67/1.11  tff(c_38, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_3'), '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12, c_29])).
% 1.67/1.11  tff(c_42, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_3'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_38])).
% 1.67/1.11  tff(c_67, plain, (k5_relat_1('#skF_2', k5_relat_1('#skF_3', '#skF_4'))='#skF_4' | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_58, c_42])).
% 1.67/1.11  tff(c_91, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_16, c_53, c_10, c_67])).
% 1.67/1.11  tff(c_93, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_91])).
% 1.67/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.11  
% 1.67/1.11  Inference rules
% 1.67/1.11  ----------------------
% 1.67/1.11  #Ref     : 0
% 1.67/1.11  #Sup     : 22
% 1.67/1.11  #Fact    : 0
% 1.67/1.11  #Define  : 0
% 1.67/1.11  #Split   : 0
% 1.67/1.11  #Chain   : 0
% 1.67/1.11  #Close   : 0
% 1.67/1.11  
% 1.67/1.11  Ordering : KBO
% 1.67/1.11  
% 1.67/1.11  Simplification rules
% 1.67/1.11  ----------------------
% 1.67/1.11  #Subsume      : 0
% 1.67/1.11  #Demod        : 7
% 1.67/1.11  #Tautology    : 11
% 1.67/1.11  #SimpNegUnit  : 1
% 1.67/1.11  #BackRed      : 0
% 1.67/1.11  
% 1.67/1.11  #Partial instantiations: 0
% 1.67/1.11  #Strategies tried      : 1
% 1.67/1.11  
% 1.67/1.11  Timing (in seconds)
% 1.67/1.11  ----------------------
% 1.67/1.11  Preprocessing        : 0.27
% 1.67/1.11  Parsing              : 0.14
% 1.67/1.11  CNF conversion       : 0.02
% 1.67/1.11  Main loop            : 0.09
% 1.67/1.11  Inferencing          : 0.04
% 1.67/1.12  Reduction            : 0.03
% 1.67/1.12  Demodulation         : 0.02
% 1.67/1.12  BG Simplification    : 0.01
% 1.67/1.12  Subsumption          : 0.01
% 1.67/1.12  Abstraction          : 0.01
% 1.67/1.12  MUC search           : 0.00
% 1.67/1.12  Cooper               : 0.00
% 1.67/1.12  Total                : 0.39
% 1.67/1.12  Index Insertion      : 0.00
% 1.67/1.12  Index Deletion       : 0.00
% 1.67/1.12  Index Matching       : 0.00
% 1.67/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
