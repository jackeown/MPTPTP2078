%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:44 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   42 (  48 expanded)
%              Number of leaves         :   22 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   50 (  60 expanded)
%              Number of equality atoms :   16 (  22 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k6_subset_1(C,k7_relat_1(C,B)),A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

tff(f_31,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,k4_xboole_0(B,C))
     => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( v1_relat_1(k4_xboole_0(A_9,B_10))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_37,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(A_23,B_24) = k1_xboole_0
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_45,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_37])).

tff(c_55,plain,(
    ! [B_27,A_28,C_29] :
      ( r1_xboole_0(B_27,k4_xboole_0(A_28,C_29))
      | ~ r1_xboole_0(A_28,k4_xboole_0(B_27,C_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_57,plain,(
    ! [A_28] :
      ( r1_xboole_0('#skF_1',k4_xboole_0(A_28,'#skF_2'))
      | ~ r1_xboole_0(A_28,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_55])).

tff(c_59,plain,(
    ! [A_28] : r1_xboole_0('#skF_1',k4_xboole_0(A_28,'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_57])).

tff(c_10,plain,(
    ! [A_7,B_8] : k6_subset_1(A_7,B_8) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [B_15,A_14] :
      ( k1_relat_1(k6_subset_1(B_15,k7_relat_1(B_15,A_14))) = k6_subset_1(k1_relat_1(B_15),A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_68,plain,(
    ! [B_31,A_32] :
      ( k1_relat_1(k4_xboole_0(B_31,k7_relat_1(B_31,A_32))) = k4_xboole_0(k1_relat_1(B_31),A_32)
      | ~ v1_relat_1(B_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_16])).

tff(c_14,plain,(
    ! [A_11,B_13] :
      ( k7_relat_1(A_11,B_13) = k1_xboole_0
      | ~ r1_xboole_0(B_13,k1_relat_1(A_11))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_80,plain,(
    ! [B_33,A_34,B_35] :
      ( k7_relat_1(k4_xboole_0(B_33,k7_relat_1(B_33,A_34)),B_35) = k1_xboole_0
      | ~ r1_xboole_0(B_35,k4_xboole_0(k1_relat_1(B_33),A_34))
      | ~ v1_relat_1(k4_xboole_0(B_33,k7_relat_1(B_33,A_34)))
      | ~ v1_relat_1(B_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_14])).

tff(c_87,plain,(
    ! [B_36] :
      ( k7_relat_1(k4_xboole_0(B_36,k7_relat_1(B_36,'#skF_2')),'#skF_1') = k1_xboole_0
      | ~ v1_relat_1(k4_xboole_0(B_36,k7_relat_1(B_36,'#skF_2')))
      | ~ v1_relat_1(B_36) ) ),
    inference(resolution,[status(thm)],[c_59,c_80])).

tff(c_93,plain,(
    ! [A_37] :
      ( k7_relat_1(k4_xboole_0(A_37,k7_relat_1(A_37,'#skF_2')),'#skF_1') = k1_xboole_0
      | ~ v1_relat_1(A_37) ) ),
    inference(resolution,[status(thm)],[c_12,c_87])).

tff(c_18,plain,(
    k7_relat_1(k6_subset_1('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_24,plain,(
    k7_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_18])).

tff(c_102,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_24])).

tff(c_110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_102])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:46:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.47  
% 2.16/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.47  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.16/1.47  
% 2.16/1.47  %Foreground sorts:
% 2.16/1.47  
% 2.16/1.47  
% 2.16/1.47  %Background operators:
% 2.16/1.47  
% 2.16/1.47  
% 2.16/1.47  %Foreground operators:
% 2.16/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.16/1.47  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.16/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.16/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.47  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.16/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.16/1.47  tff('#skF_1', type, '#skF_1': $i).
% 2.16/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.16/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.16/1.47  
% 2.16/1.49  tff(f_59, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k6_subset_1(C, k7_relat_1(C, B)), A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t216_relat_1)).
% 2.16/1.49  tff(f_41, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_relat_1)).
% 2.16/1.49  tff(f_31, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.16/1.49  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.16/1.49  tff(f_35, axiom, (![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_xboole_1)).
% 2.16/1.49  tff(f_37, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.16/1.49  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t212_relat_1)).
% 2.16/1.49  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 2.16/1.49  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.16/1.49  tff(c_12, plain, (![A_9, B_10]: (v1_relat_1(k4_xboole_0(A_9, B_10)) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.16/1.49  tff(c_6, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.16/1.49  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.16/1.49  tff(c_37, plain, (![A_23, B_24]: (k4_xboole_0(A_23, B_24)=k1_xboole_0 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.16/1.49  tff(c_45, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_37])).
% 2.16/1.49  tff(c_55, plain, (![B_27, A_28, C_29]: (r1_xboole_0(B_27, k4_xboole_0(A_28, C_29)) | ~r1_xboole_0(A_28, k4_xboole_0(B_27, C_29)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.16/1.49  tff(c_57, plain, (![A_28]: (r1_xboole_0('#skF_1', k4_xboole_0(A_28, '#skF_2')) | ~r1_xboole_0(A_28, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_45, c_55])).
% 2.16/1.49  tff(c_59, plain, (![A_28]: (r1_xboole_0('#skF_1', k4_xboole_0(A_28, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_57])).
% 2.16/1.49  tff(c_10, plain, (![A_7, B_8]: (k6_subset_1(A_7, B_8)=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.16/1.49  tff(c_16, plain, (![B_15, A_14]: (k1_relat_1(k6_subset_1(B_15, k7_relat_1(B_15, A_14)))=k6_subset_1(k1_relat_1(B_15), A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.16/1.49  tff(c_68, plain, (![B_31, A_32]: (k1_relat_1(k4_xboole_0(B_31, k7_relat_1(B_31, A_32)))=k4_xboole_0(k1_relat_1(B_31), A_32) | ~v1_relat_1(B_31))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_16])).
% 2.16/1.49  tff(c_14, plain, (![A_11, B_13]: (k7_relat_1(A_11, B_13)=k1_xboole_0 | ~r1_xboole_0(B_13, k1_relat_1(A_11)) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.16/1.49  tff(c_80, plain, (![B_33, A_34, B_35]: (k7_relat_1(k4_xboole_0(B_33, k7_relat_1(B_33, A_34)), B_35)=k1_xboole_0 | ~r1_xboole_0(B_35, k4_xboole_0(k1_relat_1(B_33), A_34)) | ~v1_relat_1(k4_xboole_0(B_33, k7_relat_1(B_33, A_34))) | ~v1_relat_1(B_33))), inference(superposition, [status(thm), theory('equality')], [c_68, c_14])).
% 2.16/1.49  tff(c_87, plain, (![B_36]: (k7_relat_1(k4_xboole_0(B_36, k7_relat_1(B_36, '#skF_2')), '#skF_1')=k1_xboole_0 | ~v1_relat_1(k4_xboole_0(B_36, k7_relat_1(B_36, '#skF_2'))) | ~v1_relat_1(B_36))), inference(resolution, [status(thm)], [c_59, c_80])).
% 2.16/1.49  tff(c_93, plain, (![A_37]: (k7_relat_1(k4_xboole_0(A_37, k7_relat_1(A_37, '#skF_2')), '#skF_1')=k1_xboole_0 | ~v1_relat_1(A_37))), inference(resolution, [status(thm)], [c_12, c_87])).
% 2.16/1.49  tff(c_18, plain, (k7_relat_1(k6_subset_1('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.16/1.49  tff(c_24, plain, (k7_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10, c_18])).
% 2.16/1.49  tff(c_102, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_93, c_24])).
% 2.16/1.49  tff(c_110, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_102])).
% 2.16/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.49  
% 2.16/1.49  Inference rules
% 2.16/1.49  ----------------------
% 2.16/1.49  #Ref     : 0
% 2.16/1.49  #Sup     : 20
% 2.16/1.49  #Fact    : 0
% 2.16/1.49  #Define  : 0
% 2.16/1.49  #Split   : 1
% 2.16/1.49  #Chain   : 0
% 2.16/1.49  #Close   : 0
% 2.16/1.49  
% 2.16/1.49  Ordering : KBO
% 2.16/1.49  
% 2.16/1.49  Simplification rules
% 2.16/1.49  ----------------------
% 2.16/1.49  #Subsume      : 1
% 2.16/1.49  #Demod        : 8
% 2.16/1.49  #Tautology    : 10
% 2.16/1.49  #SimpNegUnit  : 0
% 2.16/1.49  #BackRed      : 0
% 2.16/1.49  
% 2.16/1.49  #Partial instantiations: 0
% 2.16/1.49  #Strategies tried      : 1
% 2.16/1.49  
% 2.16/1.49  Timing (in seconds)
% 2.16/1.49  ----------------------
% 2.25/1.50  Preprocessing        : 0.43
% 2.25/1.50  Parsing              : 0.22
% 2.25/1.50  CNF conversion       : 0.03
% 2.25/1.50  Main loop            : 0.20
% 2.25/1.50  Inferencing          : 0.08
% 2.25/1.50  Reduction            : 0.06
% 2.25/1.50  Demodulation         : 0.04
% 2.25/1.50  BG Simplification    : 0.01
% 2.25/1.50  Subsumption          : 0.03
% 2.25/1.50  Abstraction          : 0.01
% 2.25/1.50  MUC search           : 0.00
% 2.25/1.50  Cooper               : 0.00
% 2.25/1.50  Total                : 0.67
% 2.25/1.50  Index Insertion      : 0.00
% 2.25/1.50  Index Deletion       : 0.00
% 2.25/1.50  Index Matching       : 0.00
% 2.25/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
