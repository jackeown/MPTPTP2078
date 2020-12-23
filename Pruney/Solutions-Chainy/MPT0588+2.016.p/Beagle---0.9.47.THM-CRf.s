%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:05 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   39 (  61 expanded)
%              Number of leaves         :   19 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   44 (  69 expanded)
%              Number of equality atoms :   22 (  42 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_33,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    ! [A_20,B_21] : k1_setfam_1(k2_tarski(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_96,plain,(
    ! [B_24,A_25] : k1_setfam_1(k2_tarski(B_24,A_25)) = k3_xboole_0(A_25,B_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_68])).

tff(c_6,plain,(
    ! [A_5,B_6] : k1_setfam_1(k2_tarski(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_102,plain,(
    ! [B_24,A_25] : k3_xboole_0(B_24,A_25) = k3_xboole_0(A_25,B_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_6])).

tff(c_10,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k7_relat_1(B_11,A_10),B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_63,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_67,plain,(
    ! [B_11,A_10] :
      ( k3_xboole_0(k7_relat_1(B_11,A_10),B_11) = k7_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(resolution,[status(thm)],[c_10,c_63])).

tff(c_182,plain,(
    ! [B_11,A_10] :
      ( k3_xboole_0(B_11,k7_relat_1(B_11,A_10)) = k7_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_67])).

tff(c_12,plain,(
    ! [A_12] :
      ( k7_relat_1(A_12,k1_relat_1(A_12)) = A_12
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_154,plain,(
    ! [C_28,A_29,B_30] :
      ( k3_xboole_0(k7_relat_1(C_28,A_29),k7_relat_1(C_28,B_30)) = k7_relat_1(C_28,k3_xboole_0(A_29,B_30))
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_178,plain,(
    ! [A_12,A_29] :
      ( k7_relat_1(A_12,k3_xboole_0(A_29,k1_relat_1(A_12))) = k3_xboole_0(k7_relat_1(A_12,A_29),A_12)
      | ~ v1_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_154])).

tff(c_514,plain,(
    ! [A_48,A_49] :
      ( k7_relat_1(A_48,k3_xboole_0(A_49,k1_relat_1(A_48))) = k3_xboole_0(A_48,k7_relat_1(A_48,A_49))
      | ~ v1_relat_1(A_48)
      | ~ v1_relat_1(A_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_178])).

tff(c_14,plain,(
    k7_relat_1('#skF_2',k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k7_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_119,plain,(
    k7_relat_1('#skF_2',k3_xboole_0('#skF_1',k1_relat_1('#skF_2'))) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_14])).

tff(c_551,plain,
    ( k3_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1')) != k7_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_514,c_119])).

tff(c_581,plain,(
    k3_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1')) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_551])).

tff(c_586,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_581])).

tff(c_590,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_586])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:19:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.32  
% 2.49/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.32  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.49/1.32  
% 2.49/1.32  %Foreground sorts:
% 2.49/1.32  
% 2.49/1.32  
% 2.49/1.32  %Background operators:
% 2.49/1.32  
% 2.49/1.32  
% 2.49/1.32  %Foreground operators:
% 2.49/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.32  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.49/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.49/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.49/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.49/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.49/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.49/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.49/1.32  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.49/1.32  
% 2.49/1.33  tff(f_50, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 2.49/1.33  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.49/1.33  tff(f_33, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.49/1.33  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 2.49/1.33  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.49/1.33  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 2.49/1.33  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_relat_1)).
% 2.49/1.33  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.49/1.33  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.49/1.33  tff(c_68, plain, (![A_20, B_21]: (k1_setfam_1(k2_tarski(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.49/1.33  tff(c_96, plain, (![B_24, A_25]: (k1_setfam_1(k2_tarski(B_24, A_25))=k3_xboole_0(A_25, B_24))), inference(superposition, [status(thm), theory('equality')], [c_4, c_68])).
% 2.49/1.33  tff(c_6, plain, (![A_5, B_6]: (k1_setfam_1(k2_tarski(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.49/1.33  tff(c_102, plain, (![B_24, A_25]: (k3_xboole_0(B_24, A_25)=k3_xboole_0(A_25, B_24))), inference(superposition, [status(thm), theory('equality')], [c_96, c_6])).
% 2.49/1.33  tff(c_10, plain, (![B_11, A_10]: (r1_tarski(k7_relat_1(B_11, A_10), B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.49/1.33  tff(c_63, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=A_18 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.49/1.33  tff(c_67, plain, (![B_11, A_10]: (k3_xboole_0(k7_relat_1(B_11, A_10), B_11)=k7_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(resolution, [status(thm)], [c_10, c_63])).
% 2.49/1.33  tff(c_182, plain, (![B_11, A_10]: (k3_xboole_0(B_11, k7_relat_1(B_11, A_10))=k7_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_67])).
% 2.49/1.33  tff(c_12, plain, (![A_12]: (k7_relat_1(A_12, k1_relat_1(A_12))=A_12 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.49/1.33  tff(c_154, plain, (![C_28, A_29, B_30]: (k3_xboole_0(k7_relat_1(C_28, A_29), k7_relat_1(C_28, B_30))=k7_relat_1(C_28, k3_xboole_0(A_29, B_30)) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.49/1.33  tff(c_178, plain, (![A_12, A_29]: (k7_relat_1(A_12, k3_xboole_0(A_29, k1_relat_1(A_12)))=k3_xboole_0(k7_relat_1(A_12, A_29), A_12) | ~v1_relat_1(A_12) | ~v1_relat_1(A_12))), inference(superposition, [status(thm), theory('equality')], [c_12, c_154])).
% 2.49/1.33  tff(c_514, plain, (![A_48, A_49]: (k7_relat_1(A_48, k3_xboole_0(A_49, k1_relat_1(A_48)))=k3_xboole_0(A_48, k7_relat_1(A_48, A_49)) | ~v1_relat_1(A_48) | ~v1_relat_1(A_48))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_178])).
% 2.49/1.33  tff(c_14, plain, (k7_relat_1('#skF_2', k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.49/1.33  tff(c_119, plain, (k7_relat_1('#skF_2', k3_xboole_0('#skF_1', k1_relat_1('#skF_2')))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_14])).
% 2.49/1.33  tff(c_551, plain, (k3_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_514, c_119])).
% 2.49/1.33  tff(c_581, plain, (k3_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_551])).
% 2.49/1.33  tff(c_586, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_182, c_581])).
% 2.49/1.33  tff(c_590, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_586])).
% 2.49/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.33  
% 2.49/1.33  Inference rules
% 2.49/1.33  ----------------------
% 2.49/1.33  #Ref     : 0
% 2.49/1.33  #Sup     : 155
% 2.49/1.33  #Fact    : 0
% 2.49/1.33  #Define  : 0
% 2.49/1.33  #Split   : 0
% 2.49/1.33  #Chain   : 0
% 2.49/1.33  #Close   : 0
% 2.49/1.33  
% 2.49/1.33  Ordering : KBO
% 2.49/1.33  
% 2.49/1.33  Simplification rules
% 2.49/1.33  ----------------------
% 2.49/1.33  #Subsume      : 31
% 2.49/1.33  #Demod        : 19
% 2.49/1.33  #Tautology    : 56
% 2.49/1.33  #SimpNegUnit  : 0
% 2.49/1.33  #BackRed      : 1
% 2.49/1.33  
% 2.49/1.33  #Partial instantiations: 0
% 2.49/1.33  #Strategies tried      : 1
% 2.49/1.33  
% 2.49/1.33  Timing (in seconds)
% 2.49/1.33  ----------------------
% 2.49/1.33  Preprocessing        : 0.26
% 2.49/1.33  Parsing              : 0.15
% 2.49/1.33  CNF conversion       : 0.01
% 2.49/1.33  Main loop            : 0.31
% 2.49/1.33  Inferencing          : 0.13
% 2.49/1.33  Reduction            : 0.09
% 2.49/1.33  Demodulation         : 0.08
% 2.49/1.33  BG Simplification    : 0.02
% 2.49/1.33  Subsumption          : 0.05
% 2.49/1.33  Abstraction          : 0.02
% 2.49/1.33  MUC search           : 0.00
% 2.49/1.33  Cooper               : 0.00
% 2.49/1.33  Total                : 0.59
% 2.49/1.33  Index Insertion      : 0.00
% 2.49/1.33  Index Deletion       : 0.00
% 2.49/1.33  Index Matching       : 0.00
% 2.49/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
