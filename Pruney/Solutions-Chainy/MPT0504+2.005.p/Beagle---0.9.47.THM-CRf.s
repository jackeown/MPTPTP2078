%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:49 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   37 (  39 expanded)
%              Number of leaves         :   20 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   44 (  50 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( v1_relat_1(k7_relat_1(A_10,B_11))
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_55,plain,(
    ! [A_20,B_21] :
      ( k3_xboole_0(A_20,B_21) = A_20
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_59,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_18,c_55])).

tff(c_12,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_13,A_12)),A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_79,plain,(
    ! [A_26,B_27,C_28] :
      ( r1_tarski(A_26,B_27)
      | ~ r1_tarski(A_26,k3_xboole_0(B_27,C_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_94,plain,(
    ! [A_29,A_30,B_31] :
      ( r1_tarski(A_29,A_30)
      | ~ r1_tarski(A_29,k3_xboole_0(B_31,A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_79])).

tff(c_166,plain,(
    ! [B_39,B_40,A_41] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_39,k3_xboole_0(B_40,A_41))),A_41)
      | ~ v1_relat_1(B_39) ) ),
    inference(resolution,[status(thm)],[c_12,c_94])).

tff(c_201,plain,(
    ! [B_42] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_42,'#skF_1')),'#skF_2')
      | ~ v1_relat_1(B_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_166])).

tff(c_14,plain,(
    ! [B_15,A_14] :
      ( k7_relat_1(B_15,A_14) = B_15
      | ~ r1_tarski(k1_relat_1(B_15),A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_947,plain,(
    ! [B_92] :
      ( k7_relat_1(k7_relat_1(B_92,'#skF_1'),'#skF_2') = k7_relat_1(B_92,'#skF_1')
      | ~ v1_relat_1(k7_relat_1(B_92,'#skF_1'))
      | ~ v1_relat_1(B_92) ) ),
    inference(resolution,[status(thm)],[c_201,c_14])).

tff(c_957,plain,(
    ! [A_93] :
      ( k7_relat_1(k7_relat_1(A_93,'#skF_1'),'#skF_2') = k7_relat_1(A_93,'#skF_1')
      | ~ v1_relat_1(A_93) ) ),
    inference(resolution,[status(thm)],[c_10,c_947])).

tff(c_16,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') != k7_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_975,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_957,c_16])).

tff(c_994,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_975])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:12:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.45  
% 2.71/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.45  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.71/1.45  
% 2.71/1.45  %Foreground sorts:
% 2.71/1.45  
% 2.71/1.45  
% 2.71/1.45  %Background operators:
% 2.71/1.45  
% 2.71/1.45  
% 2.71/1.45  %Foreground operators:
% 2.71/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.45  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.71/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.71/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.71/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.71/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.71/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.71/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.71/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.71/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.71/1.45  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.71/1.45  
% 2.71/1.46  tff(f_58, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_relat_1)).
% 2.71/1.46  tff(f_41, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.71/1.46  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.71/1.46  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.71/1.46  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.71/1.46  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 2.71/1.46  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 2.71/1.46  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.71/1.46  tff(c_10, plain, (![A_10, B_11]: (v1_relat_1(k7_relat_1(A_10, B_11)) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.71/1.46  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.71/1.46  tff(c_55, plain, (![A_20, B_21]: (k3_xboole_0(A_20, B_21)=A_20 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.71/1.46  tff(c_59, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_18, c_55])).
% 2.71/1.46  tff(c_12, plain, (![B_13, A_12]: (r1_tarski(k1_relat_1(k7_relat_1(B_13, A_12)), A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.71/1.46  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.71/1.46  tff(c_79, plain, (![A_26, B_27, C_28]: (r1_tarski(A_26, B_27) | ~r1_tarski(A_26, k3_xboole_0(B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.71/1.46  tff(c_94, plain, (![A_29, A_30, B_31]: (r1_tarski(A_29, A_30) | ~r1_tarski(A_29, k3_xboole_0(B_31, A_30)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_79])).
% 2.71/1.46  tff(c_166, plain, (![B_39, B_40, A_41]: (r1_tarski(k1_relat_1(k7_relat_1(B_39, k3_xboole_0(B_40, A_41))), A_41) | ~v1_relat_1(B_39))), inference(resolution, [status(thm)], [c_12, c_94])).
% 2.71/1.46  tff(c_201, plain, (![B_42]: (r1_tarski(k1_relat_1(k7_relat_1(B_42, '#skF_1')), '#skF_2') | ~v1_relat_1(B_42))), inference(superposition, [status(thm), theory('equality')], [c_59, c_166])).
% 2.71/1.46  tff(c_14, plain, (![B_15, A_14]: (k7_relat_1(B_15, A_14)=B_15 | ~r1_tarski(k1_relat_1(B_15), A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.71/1.46  tff(c_947, plain, (![B_92]: (k7_relat_1(k7_relat_1(B_92, '#skF_1'), '#skF_2')=k7_relat_1(B_92, '#skF_1') | ~v1_relat_1(k7_relat_1(B_92, '#skF_1')) | ~v1_relat_1(B_92))), inference(resolution, [status(thm)], [c_201, c_14])).
% 2.71/1.46  tff(c_957, plain, (![A_93]: (k7_relat_1(k7_relat_1(A_93, '#skF_1'), '#skF_2')=k7_relat_1(A_93, '#skF_1') | ~v1_relat_1(A_93))), inference(resolution, [status(thm)], [c_10, c_947])).
% 2.71/1.46  tff(c_16, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')!=k7_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.71/1.46  tff(c_975, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_957, c_16])).
% 2.71/1.46  tff(c_994, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_975])).
% 2.71/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.46  
% 2.71/1.46  Inference rules
% 2.71/1.46  ----------------------
% 2.71/1.46  #Ref     : 0
% 2.71/1.46  #Sup     : 234
% 2.71/1.46  #Fact    : 0
% 2.71/1.46  #Define  : 0
% 2.71/1.46  #Split   : 0
% 2.71/1.46  #Chain   : 0
% 2.71/1.46  #Close   : 0
% 2.71/1.46  
% 2.71/1.46  Ordering : KBO
% 2.71/1.46  
% 2.71/1.46  Simplification rules
% 2.71/1.46  ----------------------
% 2.71/1.46  #Subsume      : 75
% 2.71/1.46  #Demod        : 22
% 2.71/1.46  #Tautology    : 28
% 2.71/1.46  #SimpNegUnit  : 0
% 2.71/1.46  #BackRed      : 0
% 2.71/1.46  
% 2.71/1.46  #Partial instantiations: 0
% 2.71/1.46  #Strategies tried      : 1
% 2.71/1.46  
% 2.71/1.46  Timing (in seconds)
% 2.71/1.46  ----------------------
% 2.71/1.46  Preprocessing        : 0.28
% 2.71/1.46  Parsing              : 0.16
% 2.71/1.46  CNF conversion       : 0.02
% 2.71/1.46  Main loop            : 0.39
% 2.71/1.46  Inferencing          : 0.15
% 2.71/1.46  Reduction            : 0.12
% 2.71/1.46  Demodulation         : 0.09
% 2.71/1.46  BG Simplification    : 0.02
% 2.71/1.46  Subsumption          : 0.08
% 2.71/1.46  Abstraction          : 0.02
% 2.71/1.46  MUC search           : 0.00
% 2.71/1.46  Cooper               : 0.00
% 2.71/1.46  Total                : 0.70
% 2.71/1.46  Index Insertion      : 0.00
% 2.71/1.46  Index Deletion       : 0.00
% 2.71/1.46  Index Matching       : 0.00
% 2.71/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
