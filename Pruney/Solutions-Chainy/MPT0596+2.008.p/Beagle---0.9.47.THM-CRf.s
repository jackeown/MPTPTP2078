%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:12 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   40 (  47 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :   58 (  80 expanded)
%              Number of equality atoms :   13 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( v1_relat_1(C)
           => ( r1_tarski(k2_relat_1(B),k1_relat_1(k7_relat_1(C,A)))
             => k5_relat_1(B,k7_relat_1(C,A)) = k5_relat_1(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t200_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_12,plain,(
    ! [A_16,B_17] :
      ( k5_relat_1(k6_relat_1(A_16),B_17) = k7_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4,plain,(
    ! [A_4] : v1_relat_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    r1_tarski(k2_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_10,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_15,A_14)),A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_23,plain,(
    ! [A_22,C_23,B_24] :
      ( r1_tarski(A_22,C_23)
      | ~ r1_tarski(B_24,C_23)
      | ~ r1_tarski(A_22,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    ! [A_32,A_33,B_34] :
      ( r1_tarski(A_32,A_33)
      | ~ r1_tarski(A_32,k1_relat_1(k7_relat_1(B_34,A_33)))
      | ~ v1_relat_1(B_34) ) ),
    inference(resolution,[status(thm)],[c_10,c_23])).

tff(c_80,plain,
    ( r1_tarski(k2_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_70])).

tff(c_87,plain,(
    r1_tarski(k2_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_80])).

tff(c_8,plain,(
    ! [B_13,A_12] :
      ( k5_relat_1(B_13,k6_relat_1(A_12)) = B_13
      | ~ r1_tarski(k2_relat_1(B_13),A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_90,plain,
    ( k5_relat_1('#skF_2',k6_relat_1('#skF_1')) = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_87,c_8])).

tff(c_97,plain,(
    k5_relat_1('#skF_2',k6_relat_1('#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_90])).

tff(c_105,plain,(
    ! [A_35,B_36,C_37] :
      ( k5_relat_1(k5_relat_1(A_35,B_36),C_37) = k5_relat_1(A_35,k5_relat_1(B_36,C_37))
      | ~ v1_relat_1(C_37)
      | ~ v1_relat_1(B_36)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_120,plain,(
    ! [C_37] :
      ( k5_relat_1('#skF_2',k5_relat_1(k6_relat_1('#skF_1'),C_37)) = k5_relat_1('#skF_2',C_37)
      | ~ v1_relat_1(C_37)
      | ~ v1_relat_1(k6_relat_1('#skF_1'))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_105])).

tff(c_198,plain,(
    ! [C_41] :
      ( k5_relat_1('#skF_2',k5_relat_1(k6_relat_1('#skF_1'),C_41)) = k5_relat_1('#skF_2',C_41)
      | ~ v1_relat_1(C_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_4,c_120])).

tff(c_228,plain,(
    ! [B_44] :
      ( k5_relat_1('#skF_2',k7_relat_1(B_44,'#skF_1')) = k5_relat_1('#skF_2',B_44)
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(B_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_198])).

tff(c_14,plain,(
    k5_relat_1('#skF_2',k7_relat_1('#skF_3','#skF_1')) != k5_relat_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_237,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_14])).

tff(c_247,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_237])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:54:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.58  
% 2.48/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.59  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.48/1.59  
% 2.48/1.59  %Foreground sorts:
% 2.48/1.59  
% 2.48/1.59  
% 2.48/1.59  %Background operators:
% 2.48/1.59  
% 2.48/1.59  
% 2.48/1.59  %Foreground operators:
% 2.48/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.59  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.48/1.59  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.48/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.48/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.48/1.59  tff('#skF_2', type, '#skF_2': $i).
% 2.48/1.59  tff('#skF_3', type, '#skF_3': $i).
% 2.48/1.59  tff('#skF_1', type, '#skF_1': $i).
% 2.48/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.48/1.59  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.48/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.48/1.59  
% 2.48/1.60  tff(f_67, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(k2_relat_1(B), k1_relat_1(k7_relat_1(C, A))) => (k5_relat_1(B, k7_relat_1(C, A)) = k5_relat_1(B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t200_relat_1)).
% 2.48/1.60  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.48/1.60  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.48/1.60  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.48/1.60  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.48/1.60  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 2.48/1.60  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 2.48/1.60  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.48/1.60  tff(c_12, plain, (![A_16, B_17]: (k5_relat_1(k6_relat_1(A_16), B_17)=k7_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.48/1.60  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.48/1.60  tff(c_4, plain, (![A_4]: (v1_relat_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.48/1.60  tff(c_16, plain, (r1_tarski(k2_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.48/1.60  tff(c_10, plain, (![B_15, A_14]: (r1_tarski(k1_relat_1(k7_relat_1(B_15, A_14)), A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.48/1.60  tff(c_23, plain, (![A_22, C_23, B_24]: (r1_tarski(A_22, C_23) | ~r1_tarski(B_24, C_23) | ~r1_tarski(A_22, B_24))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.48/1.60  tff(c_70, plain, (![A_32, A_33, B_34]: (r1_tarski(A_32, A_33) | ~r1_tarski(A_32, k1_relat_1(k7_relat_1(B_34, A_33))) | ~v1_relat_1(B_34))), inference(resolution, [status(thm)], [c_10, c_23])).
% 2.48/1.60  tff(c_80, plain, (r1_tarski(k2_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_70])).
% 2.48/1.60  tff(c_87, plain, (r1_tarski(k2_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_80])).
% 2.48/1.60  tff(c_8, plain, (![B_13, A_12]: (k5_relat_1(B_13, k6_relat_1(A_12))=B_13 | ~r1_tarski(k2_relat_1(B_13), A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.48/1.60  tff(c_90, plain, (k5_relat_1('#skF_2', k6_relat_1('#skF_1'))='#skF_2' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_87, c_8])).
% 2.48/1.60  tff(c_97, plain, (k5_relat_1('#skF_2', k6_relat_1('#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_90])).
% 2.48/1.60  tff(c_105, plain, (![A_35, B_36, C_37]: (k5_relat_1(k5_relat_1(A_35, B_36), C_37)=k5_relat_1(A_35, k5_relat_1(B_36, C_37)) | ~v1_relat_1(C_37) | ~v1_relat_1(B_36) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.48/1.60  tff(c_120, plain, (![C_37]: (k5_relat_1('#skF_2', k5_relat_1(k6_relat_1('#skF_1'), C_37))=k5_relat_1('#skF_2', C_37) | ~v1_relat_1(C_37) | ~v1_relat_1(k6_relat_1('#skF_1')) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_97, c_105])).
% 2.48/1.60  tff(c_198, plain, (![C_41]: (k5_relat_1('#skF_2', k5_relat_1(k6_relat_1('#skF_1'), C_41))=k5_relat_1('#skF_2', C_41) | ~v1_relat_1(C_41))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_4, c_120])).
% 2.48/1.60  tff(c_228, plain, (![B_44]: (k5_relat_1('#skF_2', k7_relat_1(B_44, '#skF_1'))=k5_relat_1('#skF_2', B_44) | ~v1_relat_1(B_44) | ~v1_relat_1(B_44))), inference(superposition, [status(thm), theory('equality')], [c_12, c_198])).
% 2.48/1.60  tff(c_14, plain, (k5_relat_1('#skF_2', k7_relat_1('#skF_3', '#skF_1'))!=k5_relat_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.48/1.60  tff(c_237, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_228, c_14])).
% 2.48/1.60  tff(c_247, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_237])).
% 2.48/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.60  
% 2.48/1.60  Inference rules
% 2.48/1.60  ----------------------
% 2.48/1.60  #Ref     : 0
% 2.48/1.60  #Sup     : 49
% 2.48/1.60  #Fact    : 0
% 2.48/1.60  #Define  : 0
% 2.48/1.60  #Split   : 0
% 2.48/1.61  #Chain   : 0
% 2.48/1.61  #Close   : 0
% 2.48/1.61  
% 2.48/1.61  Ordering : KBO
% 2.48/1.61  
% 2.48/1.61  Simplification rules
% 2.48/1.61  ----------------------
% 2.48/1.61  #Subsume      : 2
% 2.48/1.61  #Demod        : 27
% 2.48/1.61  #Tautology    : 18
% 2.48/1.61  #SimpNegUnit  : 0
% 2.48/1.61  #BackRed      : 0
% 2.48/1.61  
% 2.48/1.61  #Partial instantiations: 0
% 2.48/1.61  #Strategies tried      : 1
% 2.48/1.61  
% 2.48/1.61  Timing (in seconds)
% 2.48/1.61  ----------------------
% 2.48/1.61  Preprocessing        : 0.45
% 2.48/1.61  Parsing              : 0.25
% 2.48/1.61  CNF conversion       : 0.03
% 2.48/1.61  Main loop            : 0.34
% 2.48/1.61  Inferencing          : 0.13
% 2.48/1.61  Reduction            : 0.10
% 2.48/1.61  Demodulation         : 0.07
% 2.48/1.61  BG Simplification    : 0.02
% 2.48/1.61  Subsumption          : 0.07
% 2.48/1.61  Abstraction          : 0.02
% 2.48/1.61  MUC search           : 0.00
% 2.48/1.61  Cooper               : 0.00
% 2.48/1.61  Total                : 0.83
% 2.48/1.61  Index Insertion      : 0.00
% 2.48/1.61  Index Deletion       : 0.00
% 2.48/1.61  Index Matching       : 0.00
% 2.48/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
