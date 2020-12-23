%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:11 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   42 (  49 expanded)
%              Number of leaves         :   21 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :   44 (  59 expanded)
%              Number of equality atoms :   22 (  28 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_53,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B,C] :
            ( r1_tarski(B,C)
           => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_33,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [B_13,A_12] :
      ( k2_relat_1(k7_relat_1(B_13,A_12)) = k9_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k7_relat_1(A_7,B_8))
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,(
    ! [A_22,B_23] : k1_setfam_1(k2_tarski(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_77,plain,(
    ! [B_24,A_25] : k1_setfam_1(k2_tarski(B_24,A_25)) = k3_xboole_0(A_25,B_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_58])).

tff(c_6,plain,(
    ! [A_5,B_6] : k1_setfam_1(k2_tarski(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_100,plain,(
    ! [B_26,A_27] : k3_xboole_0(B_26,A_27) = k3_xboole_0(A_27,B_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_6])).

tff(c_16,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_53,plain,(
    ! [A_20,B_21] :
      ( k3_xboole_0(A_20,B_21) = A_20
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_57,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_16,c_53])).

tff(c_115,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_57])).

tff(c_162,plain,(
    ! [C_30,A_31,B_32] :
      ( k7_relat_1(k7_relat_1(C_30,A_31),B_32) = k7_relat_1(C_30,k3_xboole_0(A_31,B_32))
      | ~ v1_relat_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_183,plain,(
    ! [C_33,A_34,B_35] :
      ( k2_relat_1(k7_relat_1(C_33,k3_xboole_0(A_34,B_35))) = k9_relat_1(k7_relat_1(C_33,A_34),B_35)
      | ~ v1_relat_1(k7_relat_1(C_33,A_34))
      | ~ v1_relat_1(C_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_12])).

tff(c_238,plain,(
    ! [C_38] :
      ( k9_relat_1(k7_relat_1(C_38,'#skF_3'),'#skF_2') = k2_relat_1(k7_relat_1(C_38,'#skF_2'))
      | ~ v1_relat_1(k7_relat_1(C_38,'#skF_3'))
      | ~ v1_relat_1(C_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_183])).

tff(c_248,plain,(
    ! [A_39] :
      ( k9_relat_1(k7_relat_1(A_39,'#skF_3'),'#skF_2') = k2_relat_1(k7_relat_1(A_39,'#skF_2'))
      | ~ v1_relat_1(A_39) ) ),
    inference(resolution,[status(thm)],[c_8,c_238])).

tff(c_14,plain,(
    k9_relat_1(k7_relat_1('#skF_1','#skF_3'),'#skF_2') != k9_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_254,plain,
    ( k2_relat_1(k7_relat_1('#skF_1','#skF_2')) != k9_relat_1('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_14])).

tff(c_264,plain,(
    k2_relat_1(k7_relat_1('#skF_1','#skF_2')) != k9_relat_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_254])).

tff(c_268,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_264])).

tff(c_272,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_268])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:51:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.34  
% 2.04/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.35  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 2.04/1.35  
% 2.04/1.35  %Foreground sorts:
% 2.04/1.35  
% 2.04/1.35  
% 2.04/1.35  %Background operators:
% 2.04/1.35  
% 2.04/1.35  
% 2.04/1.35  %Foreground operators:
% 2.04/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.35  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.04/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.04/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.04/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.04/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.04/1.35  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.04/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.04/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.04/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.04/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.04/1.35  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.04/1.35  
% 2.04/1.36  tff(f_53, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 2.04/1.36  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.04/1.36  tff(f_37, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.04/1.36  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.04/1.36  tff(f_33, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.04/1.36  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.04/1.36  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 2.04/1.36  tff(c_18, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.04/1.36  tff(c_12, plain, (![B_13, A_12]: (k2_relat_1(k7_relat_1(B_13, A_12))=k9_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.04/1.36  tff(c_8, plain, (![A_7, B_8]: (v1_relat_1(k7_relat_1(A_7, B_8)) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.04/1.36  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.04/1.36  tff(c_58, plain, (![A_22, B_23]: (k1_setfam_1(k2_tarski(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.04/1.36  tff(c_77, plain, (![B_24, A_25]: (k1_setfam_1(k2_tarski(B_24, A_25))=k3_xboole_0(A_25, B_24))), inference(superposition, [status(thm), theory('equality')], [c_4, c_58])).
% 2.04/1.36  tff(c_6, plain, (![A_5, B_6]: (k1_setfam_1(k2_tarski(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.04/1.36  tff(c_100, plain, (![B_26, A_27]: (k3_xboole_0(B_26, A_27)=k3_xboole_0(A_27, B_26))), inference(superposition, [status(thm), theory('equality')], [c_77, c_6])).
% 2.04/1.36  tff(c_16, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.04/1.36  tff(c_53, plain, (![A_20, B_21]: (k3_xboole_0(A_20, B_21)=A_20 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.04/1.36  tff(c_57, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_16, c_53])).
% 2.04/1.36  tff(c_115, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_100, c_57])).
% 2.04/1.36  tff(c_162, plain, (![C_30, A_31, B_32]: (k7_relat_1(k7_relat_1(C_30, A_31), B_32)=k7_relat_1(C_30, k3_xboole_0(A_31, B_32)) | ~v1_relat_1(C_30))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.04/1.36  tff(c_183, plain, (![C_33, A_34, B_35]: (k2_relat_1(k7_relat_1(C_33, k3_xboole_0(A_34, B_35)))=k9_relat_1(k7_relat_1(C_33, A_34), B_35) | ~v1_relat_1(k7_relat_1(C_33, A_34)) | ~v1_relat_1(C_33))), inference(superposition, [status(thm), theory('equality')], [c_162, c_12])).
% 2.04/1.36  tff(c_238, plain, (![C_38]: (k9_relat_1(k7_relat_1(C_38, '#skF_3'), '#skF_2')=k2_relat_1(k7_relat_1(C_38, '#skF_2')) | ~v1_relat_1(k7_relat_1(C_38, '#skF_3')) | ~v1_relat_1(C_38))), inference(superposition, [status(thm), theory('equality')], [c_115, c_183])).
% 2.04/1.36  tff(c_248, plain, (![A_39]: (k9_relat_1(k7_relat_1(A_39, '#skF_3'), '#skF_2')=k2_relat_1(k7_relat_1(A_39, '#skF_2')) | ~v1_relat_1(A_39))), inference(resolution, [status(thm)], [c_8, c_238])).
% 2.04/1.36  tff(c_14, plain, (k9_relat_1(k7_relat_1('#skF_1', '#skF_3'), '#skF_2')!=k9_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.04/1.36  tff(c_254, plain, (k2_relat_1(k7_relat_1('#skF_1', '#skF_2'))!=k9_relat_1('#skF_1', '#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_248, c_14])).
% 2.04/1.36  tff(c_264, plain, (k2_relat_1(k7_relat_1('#skF_1', '#skF_2'))!=k9_relat_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_254])).
% 2.04/1.36  tff(c_268, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_12, c_264])).
% 2.04/1.36  tff(c_272, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_268])).
% 2.04/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.36  
% 2.04/1.36  Inference rules
% 2.04/1.36  ----------------------
% 2.04/1.36  #Ref     : 0
% 2.04/1.36  #Sup     : 64
% 2.04/1.36  #Fact    : 0
% 2.04/1.36  #Define  : 0
% 2.04/1.36  #Split   : 0
% 2.04/1.36  #Chain   : 0
% 2.04/1.36  #Close   : 0
% 2.04/1.36  
% 2.04/1.36  Ordering : KBO
% 2.04/1.36  
% 2.04/1.36  Simplification rules
% 2.04/1.36  ----------------------
% 2.04/1.36  #Subsume      : 4
% 2.04/1.36  #Demod        : 8
% 2.04/1.36  #Tautology    : 40
% 2.04/1.36  #SimpNegUnit  : 0
% 2.04/1.36  #BackRed      : 0
% 2.04/1.36  
% 2.04/1.36  #Partial instantiations: 0
% 2.04/1.36  #Strategies tried      : 1
% 2.04/1.36  
% 2.04/1.36  Timing (in seconds)
% 2.04/1.36  ----------------------
% 2.04/1.36  Preprocessing        : 0.31
% 2.04/1.36  Parsing              : 0.17
% 2.04/1.36  CNF conversion       : 0.02
% 2.04/1.36  Main loop            : 0.20
% 2.04/1.36  Inferencing          : 0.08
% 2.04/1.36  Reduction            : 0.06
% 2.04/1.36  Demodulation         : 0.05
% 2.04/1.36  BG Simplification    : 0.01
% 2.04/1.36  Subsumption          : 0.04
% 2.04/1.36  Abstraction          : 0.01
% 2.04/1.36  MUC search           : 0.00
% 2.04/1.36  Cooper               : 0.00
% 2.04/1.36  Total                : 0.54
% 2.04/1.36  Index Insertion      : 0.00
% 2.04/1.36  Index Deletion       : 0.00
% 2.04/1.36  Index Matching       : 0.00
% 2.04/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
