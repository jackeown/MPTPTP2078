%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:52 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   45 (  49 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   47 (  60 expanded)
%              Number of equality atoms :   31 (  38 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k1_relat_1(B))
            & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_41,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_22,plain,(
    k9_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_14,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_90,plain,(
    ! [A_23,B_24] : k1_setfam_1(k2_tarski(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_110,plain,(
    ! [B_27,A_28] : k1_setfam_1(k2_tarski(B_27,A_28)) = k3_xboole_0(A_28,B_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_90])).

tff(c_16,plain,(
    ! [A_10,B_11] : k1_setfam_1(k2_tarski(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_116,plain,(
    ! [B_27,A_28] : k3_xboole_0(B_27,A_28) = k3_xboole_0(A_28,B_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_16])).

tff(c_216,plain,(
    ! [B_34,A_35] :
      ( r1_xboole_0(k1_relat_1(B_34),A_35)
      | k9_relat_1(B_34,A_35) != k1_xboole_0
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_558,plain,(
    ! [B_47,A_48] :
      ( k3_xboole_0(k1_relat_1(B_47),A_48) = k1_xboole_0
      | k9_relat_1(B_47,A_48) != k1_xboole_0
      | ~ v1_relat_1(B_47) ) ),
    inference(resolution,[status(thm)],[c_216,c_2])).

tff(c_664,plain,(
    ! [A_51,B_52] :
      ( k3_xboole_0(A_51,k1_relat_1(B_52)) = k1_xboole_0
      | k9_relat_1(B_52,A_51) != k1_xboole_0
      | ~ v1_relat_1(B_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_558])).

tff(c_10,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_24,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_75,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = k1_xboole_0
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_79,plain,(
    k4_xboole_0('#skF_1',k1_relat_1('#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_75])).

tff(c_166,plain,(
    ! [A_31,B_32] : k4_xboole_0(A_31,k4_xboole_0(A_31,B_32)) = k3_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_181,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_166])).

tff(c_187,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_181])).

tff(c_696,plain,
    ( k1_xboole_0 = '#skF_1'
    | k9_relat_1('#skF_2','#skF_1') != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_664,c_187])).

tff(c_730,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_22,c_696])).

tff(c_732,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_730])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:04:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.38  
% 2.47/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.39  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.47/1.39  
% 2.47/1.39  %Foreground sorts:
% 2.47/1.39  
% 2.47/1.39  
% 2.47/1.39  %Background operators:
% 2.47/1.39  
% 2.47/1.39  
% 2.47/1.39  %Foreground operators:
% 2.47/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.47/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.47/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.47/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.47/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.47/1.39  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.47/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.47/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.47/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.47/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.47/1.39  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.47/1.39  
% 2.47/1.39  tff(f_58, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_relat_1)).
% 2.47/1.39  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.47/1.39  tff(f_41, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.47/1.39  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 2.47/1.39  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.47/1.39  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.47/1.39  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.47/1.39  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.47/1.39  tff(c_26, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.47/1.39  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.47/1.39  tff(c_22, plain, (k9_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.47/1.39  tff(c_14, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.47/1.39  tff(c_90, plain, (![A_23, B_24]: (k1_setfam_1(k2_tarski(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.47/1.39  tff(c_110, plain, (![B_27, A_28]: (k1_setfam_1(k2_tarski(B_27, A_28))=k3_xboole_0(A_28, B_27))), inference(superposition, [status(thm), theory('equality')], [c_14, c_90])).
% 2.47/1.39  tff(c_16, plain, (![A_10, B_11]: (k1_setfam_1(k2_tarski(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.47/1.39  tff(c_116, plain, (![B_27, A_28]: (k3_xboole_0(B_27, A_28)=k3_xboole_0(A_28, B_27))), inference(superposition, [status(thm), theory('equality')], [c_110, c_16])).
% 2.47/1.39  tff(c_216, plain, (![B_34, A_35]: (r1_xboole_0(k1_relat_1(B_34), A_35) | k9_relat_1(B_34, A_35)!=k1_xboole_0 | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.47/1.39  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.47/1.39  tff(c_558, plain, (![B_47, A_48]: (k3_xboole_0(k1_relat_1(B_47), A_48)=k1_xboole_0 | k9_relat_1(B_47, A_48)!=k1_xboole_0 | ~v1_relat_1(B_47))), inference(resolution, [status(thm)], [c_216, c_2])).
% 2.47/1.39  tff(c_664, plain, (![A_51, B_52]: (k3_xboole_0(A_51, k1_relat_1(B_52))=k1_xboole_0 | k9_relat_1(B_52, A_51)!=k1_xboole_0 | ~v1_relat_1(B_52))), inference(superposition, [status(thm), theory('equality')], [c_116, c_558])).
% 2.47/1.39  tff(c_10, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.47/1.39  tff(c_24, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.47/1.39  tff(c_75, plain, (![A_17, B_18]: (k4_xboole_0(A_17, B_18)=k1_xboole_0 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.47/1.39  tff(c_79, plain, (k4_xboole_0('#skF_1', k1_relat_1('#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_75])).
% 2.47/1.39  tff(c_166, plain, (![A_31, B_32]: (k4_xboole_0(A_31, k4_xboole_0(A_31, B_32))=k3_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.47/1.39  tff(c_181, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_79, c_166])).
% 2.47/1.39  tff(c_187, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_181])).
% 2.47/1.39  tff(c_696, plain, (k1_xboole_0='#skF_1' | k9_relat_1('#skF_2', '#skF_1')!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_664, c_187])).
% 2.47/1.39  tff(c_730, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_22, c_696])).
% 2.47/1.39  tff(c_732, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_730])).
% 2.47/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.39  
% 2.47/1.39  Inference rules
% 2.47/1.39  ----------------------
% 2.47/1.39  #Ref     : 0
% 2.47/1.40  #Sup     : 170
% 2.47/1.40  #Fact    : 0
% 2.47/1.40  #Define  : 0
% 2.47/1.40  #Split   : 0
% 2.47/1.40  #Chain   : 0
% 2.47/1.40  #Close   : 0
% 2.47/1.40  
% 2.47/1.40  Ordering : KBO
% 2.47/1.40  
% 2.47/1.40  Simplification rules
% 2.47/1.40  ----------------------
% 2.47/1.40  #Subsume      : 13
% 2.47/1.40  #Demod        : 93
% 2.47/1.40  #Tautology    : 103
% 2.47/1.40  #SimpNegUnit  : 1
% 2.47/1.40  #BackRed      : 0
% 2.47/1.40  
% 2.47/1.40  #Partial instantiations: 0
% 2.47/1.40  #Strategies tried      : 1
% 2.47/1.40  
% 2.47/1.40  Timing (in seconds)
% 2.47/1.40  ----------------------
% 2.47/1.40  Preprocessing        : 0.28
% 2.47/1.40  Parsing              : 0.15
% 2.47/1.40  CNF conversion       : 0.02
% 2.47/1.40  Main loop            : 0.30
% 2.47/1.40  Inferencing          : 0.11
% 2.47/1.40  Reduction            : 0.12
% 2.47/1.40  Demodulation         : 0.09
% 2.47/1.40  BG Simplification    : 0.02
% 2.47/1.40  Subsumption          : 0.05
% 2.47/1.40  Abstraction          : 0.01
% 2.47/1.40  MUC search           : 0.00
% 2.47/1.40  Cooper               : 0.00
% 2.47/1.40  Total                : 0.61
% 2.47/1.40  Index Insertion      : 0.00
% 2.47/1.40  Index Deletion       : 0.00
% 2.47/1.40  Index Matching       : 0.00
% 2.47/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
