%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:52 EST 2020

% Result     : Theorem 1.57s
% Output     : CNFRefutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   30 (  33 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    4
%              Number of atoms          :   25 (  32 expanded)
%              Number of equality atoms :   15 (  18 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_33,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_63,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_67,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_12,c_63])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ! [A_12,B_13] : k1_setfam_1(k2_tarski(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_72,plain,(
    ! [B_16,A_17] : k1_setfam_1(k2_tarski(B_16,A_17)) = k3_xboole_0(A_17,B_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_48])).

tff(c_6,plain,(
    ! [A_5,B_6] : k1_setfam_1(k2_tarski(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_78,plain,(
    ! [B_16,A_17] : k3_xboole_0(B_16,A_17) = k3_xboole_0(A_17,B_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_6])).

tff(c_128,plain,(
    ! [C_20,A_21,B_22] :
      ( k7_relat_1(k7_relat_1(C_20,A_21),B_22) = k7_relat_1(C_20,k3_xboole_0(A_21,B_22))
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_2'),'#skF_1') != k7_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_137,plain,
    ( k7_relat_1('#skF_3',k3_xboole_0('#skF_2','#skF_1')) != k7_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_10])).

tff(c_147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_67,c_78,c_137])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:33:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.57/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.57/1.16  
% 1.57/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.57/1.16  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 1.57/1.16  
% 1.57/1.16  %Foreground sorts:
% 1.57/1.16  
% 1.57/1.16  
% 1.57/1.16  %Background operators:
% 1.57/1.16  
% 1.57/1.16  
% 1.57/1.16  %Foreground operators:
% 1.57/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.57/1.16  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.57/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.57/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.57/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.57/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.57/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.57/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.57/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.57/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.57/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.57/1.16  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.57/1.16  
% 1.57/1.17  tff(f_44, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_relat_1)).
% 1.57/1.17  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.57/1.17  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.57/1.17  tff(f_33, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.57/1.17  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 1.57/1.17  tff(c_14, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.57/1.17  tff(c_12, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.57/1.17  tff(c_63, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.57/1.17  tff(c_67, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_12, c_63])).
% 1.57/1.17  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.57/1.17  tff(c_48, plain, (![A_12, B_13]: (k1_setfam_1(k2_tarski(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.57/1.17  tff(c_72, plain, (![B_16, A_17]: (k1_setfam_1(k2_tarski(B_16, A_17))=k3_xboole_0(A_17, B_16))), inference(superposition, [status(thm), theory('equality')], [c_4, c_48])).
% 1.57/1.17  tff(c_6, plain, (![A_5, B_6]: (k1_setfam_1(k2_tarski(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.57/1.17  tff(c_78, plain, (![B_16, A_17]: (k3_xboole_0(B_16, A_17)=k3_xboole_0(A_17, B_16))), inference(superposition, [status(thm), theory('equality')], [c_72, c_6])).
% 1.57/1.17  tff(c_128, plain, (![C_20, A_21, B_22]: (k7_relat_1(k7_relat_1(C_20, A_21), B_22)=k7_relat_1(C_20, k3_xboole_0(A_21, B_22)) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.57/1.17  tff(c_10, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_2'), '#skF_1')!=k7_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.57/1.17  tff(c_137, plain, (k7_relat_1('#skF_3', k3_xboole_0('#skF_2', '#skF_1'))!=k7_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_128, c_10])).
% 1.57/1.17  tff(c_147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_67, c_78, c_137])).
% 1.57/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.57/1.17  
% 1.57/1.17  Inference rules
% 1.57/1.17  ----------------------
% 1.57/1.17  #Ref     : 0
% 1.57/1.17  #Sup     : 34
% 1.57/1.17  #Fact    : 0
% 1.57/1.17  #Define  : 0
% 1.57/1.17  #Split   : 0
% 1.57/1.17  #Chain   : 0
% 1.57/1.17  #Close   : 0
% 1.57/1.17  
% 1.57/1.17  Ordering : KBO
% 1.57/1.17  
% 1.57/1.17  Simplification rules
% 1.57/1.17  ----------------------
% 1.57/1.17  #Subsume      : 0
% 1.57/1.17  #Demod        : 5
% 1.57/1.17  #Tautology    : 25
% 1.57/1.17  #SimpNegUnit  : 0
% 1.57/1.17  #BackRed      : 0
% 1.57/1.17  
% 1.57/1.17  #Partial instantiations: 0
% 1.57/1.17  #Strategies tried      : 1
% 1.57/1.17  
% 1.57/1.17  Timing (in seconds)
% 1.57/1.17  ----------------------
% 1.57/1.17  Preprocessing        : 0.25
% 1.57/1.17  Parsing              : 0.15
% 1.57/1.17  CNF conversion       : 0.01
% 1.57/1.17  Main loop            : 0.12
% 1.57/1.17  Inferencing          : 0.05
% 1.57/1.17  Reduction            : 0.04
% 1.57/1.17  Demodulation         : 0.03
% 1.57/1.17  BG Simplification    : 0.01
% 1.57/1.17  Subsumption          : 0.01
% 1.57/1.17  Abstraction          : 0.01
% 1.57/1.17  MUC search           : 0.00
% 1.57/1.17  Cooper               : 0.00
% 1.57/1.17  Total                : 0.39
% 1.57/1.17  Index Insertion      : 0.00
% 1.57/1.17  Index Deletion       : 0.00
% 1.57/1.17  Index Matching       : 0.00
% 1.57/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
