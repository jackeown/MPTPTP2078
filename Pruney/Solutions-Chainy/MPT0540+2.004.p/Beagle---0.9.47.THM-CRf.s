%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:31 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   32 (  37 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 (  53 expanded)
%              Number of equality atoms :   12 (  15 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(f_53,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => k7_relat_1(k8_relat_1(A,C),B) = k8_relat_1(A,k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k8_relat_1(A,k5_relat_1(B,C)) = k5_relat_1(B,k8_relat_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_17,plain,(
    ! [B_15,A_16] :
      ( k5_relat_1(B_15,k6_relat_1(A_16)) = k8_relat_1(A_16,B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k5_relat_1(A_1,B_2))
      | ~ v1_relat_1(B_2)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_23,plain,(
    ! [A_16,B_15] :
      ( v1_relat_1(k8_relat_1(A_16,B_15))
      | ~ v1_relat_1(k6_relat_1(A_16))
      | ~ v1_relat_1(B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17,c_2])).

tff(c_29,plain,(
    ! [A_16,B_15] :
      ( v1_relat_1(k8_relat_1(A_16,B_15))
      | ~ v1_relat_1(B_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_23])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( k5_relat_1(k6_relat_1(A_10),B_11) = k7_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_75,plain,(
    ! [A_27,B_28,C_29] :
      ( k8_relat_1(A_27,k5_relat_1(B_28,C_29)) = k5_relat_1(B_28,k8_relat_1(A_27,C_29))
      | ~ v1_relat_1(C_29)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_87,plain,(
    ! [A_10,A_27,B_11] :
      ( k5_relat_1(k6_relat_1(A_10),k8_relat_1(A_27,B_11)) = k8_relat_1(A_27,k7_relat_1(B_11,A_10))
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(k6_relat_1(A_10))
      | ~ v1_relat_1(B_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_75])).

tff(c_97,plain,(
    ! [A_30,A_31,B_32] :
      ( k5_relat_1(k6_relat_1(A_30),k8_relat_1(A_31,B_32)) = k8_relat_1(A_31,k7_relat_1(B_32,A_30))
      | ~ v1_relat_1(B_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_87])).

tff(c_277,plain,(
    ! [A_61,B_62,A_63] :
      ( k8_relat_1(A_61,k7_relat_1(B_62,A_63)) = k7_relat_1(k8_relat_1(A_61,B_62),A_63)
      | ~ v1_relat_1(B_62)
      | ~ v1_relat_1(k8_relat_1(A_61,B_62)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_97])).

tff(c_302,plain,(
    ! [A_64,B_65,A_66] :
      ( k8_relat_1(A_64,k7_relat_1(B_65,A_66)) = k7_relat_1(k8_relat_1(A_64,B_65),A_66)
      | ~ v1_relat_1(B_65) ) ),
    inference(resolution,[status(thm)],[c_29,c_277])).

tff(c_12,plain,(
    k8_relat_1('#skF_1',k7_relat_1('#skF_3','#skF_2')) != k7_relat_1(k8_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_328,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_12])).

tff(c_346,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_328])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:12:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.29  
% 1.96/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.29  %$ v1_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.96/1.29  
% 1.96/1.29  %Foreground sorts:
% 1.96/1.29  
% 1.96/1.29  
% 1.96/1.29  %Background operators:
% 1.96/1.29  
% 1.96/1.29  
% 1.96/1.29  %Foreground operators:
% 1.96/1.29  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.96/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.29  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.96/1.29  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.96/1.29  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.29  tff('#skF_3', type, '#skF_3': $i).
% 1.96/1.29  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.96/1.29  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.96/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.29  
% 2.26/1.30  tff(f_53, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k8_relat_1(A, C), B) = k8_relat_1(A, k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_relat_1)).
% 2.26/1.30  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.26/1.30  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 2.26/1.30  tff(f_31, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.26/1.30  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.26/1.30  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k8_relat_1(A, k5_relat_1(B, C)) = k5_relat_1(B, k8_relat_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_relat_1)).
% 2.26/1.30  tff(c_14, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.26/1.30  tff(c_4, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.26/1.30  tff(c_17, plain, (![B_15, A_16]: (k5_relat_1(B_15, k6_relat_1(A_16))=k8_relat_1(A_16, B_15) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.26/1.30  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k5_relat_1(A_1, B_2)) | ~v1_relat_1(B_2) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.26/1.30  tff(c_23, plain, (![A_16, B_15]: (v1_relat_1(k8_relat_1(A_16, B_15)) | ~v1_relat_1(k6_relat_1(A_16)) | ~v1_relat_1(B_15) | ~v1_relat_1(B_15))), inference(superposition, [status(thm), theory('equality')], [c_17, c_2])).
% 2.26/1.30  tff(c_29, plain, (![A_16, B_15]: (v1_relat_1(k8_relat_1(A_16, B_15)) | ~v1_relat_1(B_15))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_23])).
% 2.26/1.30  tff(c_10, plain, (![A_10, B_11]: (k5_relat_1(k6_relat_1(A_10), B_11)=k7_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.26/1.30  tff(c_75, plain, (![A_27, B_28, C_29]: (k8_relat_1(A_27, k5_relat_1(B_28, C_29))=k5_relat_1(B_28, k8_relat_1(A_27, C_29)) | ~v1_relat_1(C_29) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.26/1.30  tff(c_87, plain, (![A_10, A_27, B_11]: (k5_relat_1(k6_relat_1(A_10), k8_relat_1(A_27, B_11))=k8_relat_1(A_27, k7_relat_1(B_11, A_10)) | ~v1_relat_1(B_11) | ~v1_relat_1(k6_relat_1(A_10)) | ~v1_relat_1(B_11))), inference(superposition, [status(thm), theory('equality')], [c_10, c_75])).
% 2.26/1.30  tff(c_97, plain, (![A_30, A_31, B_32]: (k5_relat_1(k6_relat_1(A_30), k8_relat_1(A_31, B_32))=k8_relat_1(A_31, k7_relat_1(B_32, A_30)) | ~v1_relat_1(B_32))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_87])).
% 2.26/1.30  tff(c_277, plain, (![A_61, B_62, A_63]: (k8_relat_1(A_61, k7_relat_1(B_62, A_63))=k7_relat_1(k8_relat_1(A_61, B_62), A_63) | ~v1_relat_1(B_62) | ~v1_relat_1(k8_relat_1(A_61, B_62)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_97])).
% 2.26/1.30  tff(c_302, plain, (![A_64, B_65, A_66]: (k8_relat_1(A_64, k7_relat_1(B_65, A_66))=k7_relat_1(k8_relat_1(A_64, B_65), A_66) | ~v1_relat_1(B_65))), inference(resolution, [status(thm)], [c_29, c_277])).
% 2.26/1.30  tff(c_12, plain, (k8_relat_1('#skF_1', k7_relat_1('#skF_3', '#skF_2'))!=k7_relat_1(k8_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.26/1.30  tff(c_328, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_302, c_12])).
% 2.26/1.30  tff(c_346, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_328])).
% 2.26/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.30  
% 2.26/1.30  Inference rules
% 2.26/1.30  ----------------------
% 2.26/1.30  #Ref     : 0
% 2.26/1.30  #Sup     : 69
% 2.26/1.30  #Fact    : 0
% 2.26/1.30  #Define  : 0
% 2.26/1.30  #Split   : 0
% 2.26/1.30  #Chain   : 0
% 2.26/1.30  #Close   : 0
% 2.26/1.30  
% 2.26/1.30  Ordering : KBO
% 2.26/1.31  
% 2.26/1.31  Simplification rules
% 2.26/1.31  ----------------------
% 2.26/1.31  #Subsume      : 3
% 2.26/1.31  #Demod        : 65
% 2.26/1.31  #Tautology    : 28
% 2.26/1.31  #SimpNegUnit  : 0
% 2.26/1.31  #BackRed      : 1
% 2.26/1.31  
% 2.26/1.31  #Partial instantiations: 0
% 2.26/1.31  #Strategies tried      : 1
% 2.26/1.31  
% 2.26/1.31  Timing (in seconds)
% 2.26/1.31  ----------------------
% 2.26/1.31  Preprocessing        : 0.27
% 2.26/1.31  Parsing              : 0.15
% 2.26/1.31  CNF conversion       : 0.02
% 2.26/1.31  Main loop            : 0.24
% 2.26/1.31  Inferencing          : 0.10
% 2.26/1.31  Reduction            : 0.08
% 2.26/1.31  Demodulation         : 0.06
% 2.26/1.31  BG Simplification    : 0.01
% 2.26/1.31  Subsumption          : 0.04
% 2.26/1.31  Abstraction          : 0.02
% 2.26/1.31  MUC search           : 0.00
% 2.26/1.31  Cooper               : 0.00
% 2.26/1.31  Total                : 0.54
% 2.26/1.31  Index Insertion      : 0.00
% 2.26/1.31  Index Deletion       : 0.00
% 2.26/1.31  Index Matching       : 0.00
% 2.26/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
