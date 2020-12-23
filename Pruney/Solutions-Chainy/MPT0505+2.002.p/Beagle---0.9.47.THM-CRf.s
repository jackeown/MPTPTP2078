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
% DateTime   : Thu Dec  3 09:59:51 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   40 (  44 expanded)
%              Number of leaves         :   21 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   46 (  59 expanded)
%              Number of equality atoms :   21 (  25 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & ! [D] :
            ( ( r1_tarski(D,B)
              & r1_tarski(D,C) )
           => r1_tarski(D,A) ) )
     => A = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_52,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_26,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_186,plain,(
    ! [A_41,B_42,C_43] :
      ( r1_tarski('#skF_1'(A_41,B_42,C_43),B_42)
      | k3_xboole_0(B_42,C_43) = A_41
      | ~ r1_tarski(A_41,C_43)
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r1_tarski('#skF_1'(A_3,B_4,C_5),A_3)
      | k3_xboole_0(B_4,C_5) = A_3
      | ~ r1_tarski(A_3,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_190,plain,(
    ! [B_42,C_43] :
      ( k3_xboole_0(B_42,C_43) = B_42
      | ~ r1_tarski(B_42,C_43)
      | ~ r1_tarski(B_42,B_42) ) ),
    inference(resolution,[status(thm)],[c_186,c_8])).

tff(c_208,plain,(
    ! [B_47,C_48] :
      ( k3_xboole_0(B_47,C_48) = B_47
      | ~ r1_tarski(B_47,C_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_190])).

tff(c_226,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_26,c_208])).

tff(c_14,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_64,plain,(
    ! [A_22,B_23] : k1_setfam_1(k2_tarski(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_88,plain,(
    ! [A_26,B_27] : k1_setfam_1(k2_tarski(A_26,B_27)) = k3_xboole_0(B_27,A_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_64])).

tff(c_20,plain,(
    ! [A_14,B_15] : k1_setfam_1(k2_tarski(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_94,plain,(
    ! [B_27,A_26] : k3_xboole_0(B_27,A_26) = k3_xboole_0(A_26,B_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_20])).

tff(c_239,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_94])).

tff(c_28,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_165,plain,(
    ! [C_35,A_36,B_37] :
      ( k7_relat_1(k7_relat_1(C_35,A_36),B_37) = k7_relat_1(C_35,k3_xboole_0(A_36,B_37))
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_24,plain,(
    k7_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2') != k7_relat_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_174,plain,
    ( k7_relat_1('#skF_4',k3_xboole_0('#skF_3','#skF_2')) != k7_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_24])).

tff(c_183,plain,(
    k7_relat_1('#skF_4',k3_xboole_0('#skF_3','#skF_2')) != k7_relat_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_174])).

tff(c_254,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_183])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 15:48:06 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.39  
% 2.22/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.39  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.22/1.39  
% 2.22/1.39  %Foreground sorts:
% 2.22/1.39  
% 2.22/1.39  
% 2.22/1.39  %Background operators:
% 2.22/1.39  
% 2.22/1.39  
% 2.22/1.39  %Foreground operators:
% 2.22/1.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.22/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.39  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.22/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.22/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.22/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.22/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.22/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.22/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.22/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.22/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.22/1.39  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.22/1.39  
% 2.22/1.40  tff(f_63, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_relat_1)).
% 2.22/1.40  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.22/1.40  tff(f_44, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & (![D]: ((r1_tarski(D, B) & r1_tarski(D, C)) => r1_tarski(D, A)))) => (A = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_xboole_1)).
% 2.22/1.40  tff(f_46, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.22/1.40  tff(f_52, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.22/1.40  tff(f_56, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 2.22/1.40  tff(c_26, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.22/1.40  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.22/1.40  tff(c_186, plain, (![A_41, B_42, C_43]: (r1_tarski('#skF_1'(A_41, B_42, C_43), B_42) | k3_xboole_0(B_42, C_43)=A_41 | ~r1_tarski(A_41, C_43) | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.22/1.40  tff(c_8, plain, (![A_3, B_4, C_5]: (~r1_tarski('#skF_1'(A_3, B_4, C_5), A_3) | k3_xboole_0(B_4, C_5)=A_3 | ~r1_tarski(A_3, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.22/1.40  tff(c_190, plain, (![B_42, C_43]: (k3_xboole_0(B_42, C_43)=B_42 | ~r1_tarski(B_42, C_43) | ~r1_tarski(B_42, B_42))), inference(resolution, [status(thm)], [c_186, c_8])).
% 2.22/1.40  tff(c_208, plain, (![B_47, C_48]: (k3_xboole_0(B_47, C_48)=B_47 | ~r1_tarski(B_47, C_48))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_190])).
% 2.22/1.40  tff(c_226, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_26, c_208])).
% 2.22/1.40  tff(c_14, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.22/1.40  tff(c_64, plain, (![A_22, B_23]: (k1_setfam_1(k2_tarski(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.22/1.40  tff(c_88, plain, (![A_26, B_27]: (k1_setfam_1(k2_tarski(A_26, B_27))=k3_xboole_0(B_27, A_26))), inference(superposition, [status(thm), theory('equality')], [c_14, c_64])).
% 2.22/1.40  tff(c_20, plain, (![A_14, B_15]: (k1_setfam_1(k2_tarski(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.22/1.40  tff(c_94, plain, (![B_27, A_26]: (k3_xboole_0(B_27, A_26)=k3_xboole_0(A_26, B_27))), inference(superposition, [status(thm), theory('equality')], [c_88, c_20])).
% 2.22/1.40  tff(c_239, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_226, c_94])).
% 2.22/1.40  tff(c_28, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.22/1.40  tff(c_165, plain, (![C_35, A_36, B_37]: (k7_relat_1(k7_relat_1(C_35, A_36), B_37)=k7_relat_1(C_35, k3_xboole_0(A_36, B_37)) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.22/1.40  tff(c_24, plain, (k7_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2')!=k7_relat_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.22/1.40  tff(c_174, plain, (k7_relat_1('#skF_4', k3_xboole_0('#skF_3', '#skF_2'))!=k7_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_165, c_24])).
% 2.22/1.40  tff(c_183, plain, (k7_relat_1('#skF_4', k3_xboole_0('#skF_3', '#skF_2'))!=k7_relat_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_174])).
% 2.22/1.40  tff(c_254, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_239, c_183])).
% 2.22/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.40  
% 2.22/1.40  Inference rules
% 2.22/1.40  ----------------------
% 2.22/1.40  #Ref     : 0
% 2.22/1.40  #Sup     : 53
% 2.22/1.40  #Fact    : 0
% 2.22/1.40  #Define  : 0
% 2.22/1.40  #Split   : 1
% 2.22/1.40  #Chain   : 0
% 2.22/1.40  #Close   : 0
% 2.22/1.40  
% 2.22/1.40  Ordering : KBO
% 2.22/1.40  
% 2.22/1.40  Simplification rules
% 2.22/1.40  ----------------------
% 2.22/1.40  #Subsume      : 1
% 2.22/1.40  #Demod        : 11
% 2.22/1.40  #Tautology    : 35
% 2.22/1.40  #SimpNegUnit  : 0
% 2.22/1.40  #BackRed      : 1
% 2.22/1.40  
% 2.22/1.40  #Partial instantiations: 0
% 2.22/1.40  #Strategies tried      : 1
% 2.22/1.40  
% 2.22/1.40  Timing (in seconds)
% 2.22/1.40  ----------------------
% 2.22/1.40  Preprocessing        : 0.37
% 2.22/1.40  Parsing              : 0.18
% 2.22/1.40  CNF conversion       : 0.03
% 2.22/1.40  Main loop            : 0.19
% 2.22/1.40  Inferencing          : 0.06
% 2.22/1.40  Reduction            : 0.06
% 2.22/1.40  Demodulation         : 0.05
% 2.22/1.40  BG Simplification    : 0.01
% 2.22/1.40  Subsumption          : 0.04
% 2.22/1.40  Abstraction          : 0.01
% 2.22/1.40  MUC search           : 0.00
% 2.22/1.40  Cooper               : 0.00
% 2.22/1.40  Total                : 0.59
% 2.22/1.40  Index Insertion      : 0.00
% 2.22/1.40  Index Deletion       : 0.00
% 2.22/1.40  Index Matching       : 0.00
% 2.22/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
