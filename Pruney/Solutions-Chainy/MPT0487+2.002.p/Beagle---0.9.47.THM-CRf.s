%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:34 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   38 (  48 expanded)
%              Number of leaves         :   18 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   53 ( 111 expanded)
%              Number of equality atoms :   21 (  45 expanded)
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

tff(f_70,negated_conjecture,(
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

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(c_14,plain,(
    '#skF_2' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_22,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_16,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_84,plain,(
    ! [A_26,B_27,C_28] :
      ( k5_relat_1(k5_relat_1(A_26,B_27),C_28) = k5_relat_1(A_26,k5_relat_1(B_27,C_28))
      | ~ v1_relat_1(C_28)
      | ~ v1_relat_1(B_27)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    k6_relat_1(k1_relat_1('#skF_4')) = k5_relat_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ! [A_21,B_22] :
      ( k5_relat_1(k6_relat_1(A_21),B_22) = B_22
      | ~ r1_tarski(k1_relat_1(B_22),A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_54,plain,(
    ! [B_23] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(B_23)),B_23) = B_23
      | ~ v1_relat_1(B_23) ) ),
    inference(resolution,[status(thm)],[c_6,c_48])).

tff(c_63,plain,
    ( k5_relat_1(k5_relat_1('#skF_2','#skF_3'),'#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_54])).

tff(c_67,plain,(
    k5_relat_1(k5_relat_1('#skF_2','#skF_3'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_63])).

tff(c_93,plain,
    ( k5_relat_1('#skF_2',k5_relat_1('#skF_3','#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_67])).

tff(c_114,plain,(
    k5_relat_1('#skF_2',k6_relat_1('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_16,c_93])).

tff(c_20,plain,(
    r1_tarski(k2_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_72,plain,(
    ! [B_24,A_25] :
      ( k5_relat_1(B_24,k6_relat_1(A_25)) = B_24
      | ~ r1_tarski(k2_relat_1(B_24),A_25)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_75,plain,
    ( k5_relat_1('#skF_2',k6_relat_1('#skF_1')) = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_72])).

tff(c_82,plain,(
    k5_relat_1('#skF_2',k6_relat_1('#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_75])).

tff(c_131,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_82])).

tff(c_133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_131])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:31:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.16  
% 1.84/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.16  %$ r1_tarski > v1_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.84/1.16  
% 1.84/1.16  %Foreground sorts:
% 1.84/1.16  
% 1.84/1.16  
% 1.84/1.16  %Background operators:
% 1.84/1.16  
% 1.84/1.16  
% 1.84/1.16  %Foreground operators:
% 1.84/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.16  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.84/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.84/1.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.84/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.84/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.84/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.84/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.84/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.84/1.16  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.84/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.84/1.16  
% 1.84/1.17  tff(f_70, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => (((r1_tarski(k2_relat_1(B), A) & (k5_relat_1(B, C) = k6_relat_1(k1_relat_1(D)))) & (k5_relat_1(C, D) = k6_relat_1(A))) => (D = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_relat_1)).
% 1.84/1.17  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 1.84/1.17  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.84/1.17  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 1.84/1.17  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 1.84/1.17  tff(c_14, plain, ('#skF_2'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.84/1.17  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.84/1.17  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.84/1.17  tff(c_22, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.84/1.17  tff(c_16, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.84/1.17  tff(c_84, plain, (![A_26, B_27, C_28]: (k5_relat_1(k5_relat_1(A_26, B_27), C_28)=k5_relat_1(A_26, k5_relat_1(B_27, C_28)) | ~v1_relat_1(C_28) | ~v1_relat_1(B_27) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.84/1.17  tff(c_18, plain, (k6_relat_1(k1_relat_1('#skF_4'))=k5_relat_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.84/1.17  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.84/1.17  tff(c_48, plain, (![A_21, B_22]: (k5_relat_1(k6_relat_1(A_21), B_22)=B_22 | ~r1_tarski(k1_relat_1(B_22), A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.84/1.17  tff(c_54, plain, (![B_23]: (k5_relat_1(k6_relat_1(k1_relat_1(B_23)), B_23)=B_23 | ~v1_relat_1(B_23))), inference(resolution, [status(thm)], [c_6, c_48])).
% 1.84/1.17  tff(c_63, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_3'), '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_18, c_54])).
% 1.84/1.17  tff(c_67, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_3'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_63])).
% 1.84/1.17  tff(c_93, plain, (k5_relat_1('#skF_2', k5_relat_1('#skF_3', '#skF_4'))='#skF_4' | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_84, c_67])).
% 1.84/1.17  tff(c_114, plain, (k5_relat_1('#skF_2', k6_relat_1('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_16, c_93])).
% 1.84/1.17  tff(c_20, plain, (r1_tarski(k2_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.84/1.17  tff(c_72, plain, (![B_24, A_25]: (k5_relat_1(B_24, k6_relat_1(A_25))=B_24 | ~r1_tarski(k2_relat_1(B_24), A_25) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.84/1.17  tff(c_75, plain, (k5_relat_1('#skF_2', k6_relat_1('#skF_1'))='#skF_2' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_20, c_72])).
% 1.84/1.17  tff(c_82, plain, (k5_relat_1('#skF_2', k6_relat_1('#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_75])).
% 1.84/1.17  tff(c_131, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_114, c_82])).
% 1.84/1.17  tff(c_133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_131])).
% 1.84/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.17  
% 1.84/1.17  Inference rules
% 1.84/1.17  ----------------------
% 1.84/1.17  #Ref     : 0
% 1.84/1.17  #Sup     : 26
% 1.84/1.17  #Fact    : 0
% 1.84/1.17  #Define  : 0
% 1.84/1.17  #Split   : 1
% 1.84/1.17  #Chain   : 0
% 1.84/1.17  #Close   : 0
% 1.84/1.17  
% 1.84/1.17  Ordering : KBO
% 1.84/1.17  
% 1.84/1.17  Simplification rules
% 1.84/1.17  ----------------------
% 1.84/1.17  #Subsume      : 0
% 1.84/1.17  #Demod        : 17
% 1.84/1.17  #Tautology    : 14
% 1.84/1.17  #SimpNegUnit  : 1
% 1.84/1.17  #BackRed      : 1
% 1.84/1.17  
% 1.84/1.17  #Partial instantiations: 0
% 1.84/1.17  #Strategies tried      : 1
% 1.84/1.17  
% 1.84/1.17  Timing (in seconds)
% 1.84/1.17  ----------------------
% 1.84/1.18  Preprocessing        : 0.29
% 1.84/1.18  Parsing              : 0.16
% 1.84/1.18  CNF conversion       : 0.02
% 1.84/1.18  Main loop            : 0.12
% 1.84/1.18  Inferencing          : 0.04
% 1.84/1.18  Reduction            : 0.04
% 1.84/1.18  Demodulation         : 0.03
% 1.84/1.18  BG Simplification    : 0.01
% 1.84/1.18  Subsumption          : 0.02
% 1.84/1.18  Abstraction          : 0.01
% 1.84/1.18  MUC search           : 0.00
% 1.84/1.18  Cooper               : 0.00
% 1.84/1.18  Total                : 0.44
% 1.84/1.18  Index Insertion      : 0.00
% 1.84/1.18  Index Deletion       : 0.00
% 1.84/1.18  Index Matching       : 0.00
% 1.84/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
