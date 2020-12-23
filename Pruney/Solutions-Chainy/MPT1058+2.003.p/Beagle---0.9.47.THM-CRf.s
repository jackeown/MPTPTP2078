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
% DateTime   : Thu Dec  3 10:17:22 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   53 (  56 expanded)
%              Number of leaves         :   35 (  38 expanded)
%              Depth                    :    7
%              Number of atoms          :   33 (  42 expanded)
%              Number of equality atoms :   22 (  25 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k6_subset_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_150,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_62,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_68,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_54,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_82,plain,(
    k10_relat_1(k7_relat_1('#skF_4','#skF_5'),'#skF_6') != k10_relat_1('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_88,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_1349,plain,(
    ! [A_147,C_148,B_149] :
      ( k3_xboole_0(A_147,k10_relat_1(C_148,B_149)) = k10_relat_1(k7_relat_1(C_148,A_147),B_149)
      | ~ v1_relat_1(C_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_30,plain,(
    ! [B_21,A_20] : k2_tarski(B_21,A_20) = k2_tarski(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_329,plain,(
    ! [A_91,B_92] : k1_setfam_1(k2_tarski(A_91,B_92)) = k3_xboole_0(A_91,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_344,plain,(
    ! [B_93,A_94] : k1_setfam_1(k2_tarski(B_93,A_94)) = k3_xboole_0(A_94,B_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_329])).

tff(c_36,plain,(
    ! [A_26,B_27] : k1_setfam_1(k2_tarski(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_350,plain,(
    ! [B_93,A_94] : k3_xboole_0(B_93,A_94) = k3_xboole_0(A_94,B_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_344,c_36])).

tff(c_24,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_84,plain,(
    r1_tarski(k10_relat_1('#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_225,plain,(
    ! [A_86,B_87] :
      ( k4_xboole_0(A_86,B_87) = k1_xboole_0
      | ~ r1_tarski(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_243,plain,(
    k4_xboole_0(k10_relat_1('#skF_4','#skF_6'),'#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_84,c_225])).

tff(c_437,plain,(
    ! [A_103,B_104] : k4_xboole_0(A_103,k4_xboole_0(A_103,B_104)) = k3_xboole_0(A_103,B_104) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_465,plain,(
    k4_xboole_0(k10_relat_1('#skF_4','#skF_6'),k1_xboole_0) = k3_xboole_0(k10_relat_1('#skF_4','#skF_6'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_437])).

tff(c_482,plain,(
    k3_xboole_0('#skF_5',k10_relat_1('#skF_4','#skF_6')) = k10_relat_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_24,c_465])).

tff(c_1383,plain,
    ( k10_relat_1(k7_relat_1('#skF_4','#skF_5'),'#skF_6') = k10_relat_1('#skF_4','#skF_6')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1349,c_482])).

tff(c_1429,plain,(
    k10_relat_1(k7_relat_1('#skF_4','#skF_5'),'#skF_6') = k10_relat_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1383])).

tff(c_1431,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1429])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:45:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.48  
% 3.20/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.48  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k6_subset_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.20/1.48  
% 3.20/1.48  %Foreground sorts:
% 3.20/1.48  
% 3.20/1.48  
% 3.20/1.48  %Background operators:
% 3.20/1.48  
% 3.20/1.48  
% 3.20/1.48  %Foreground operators:
% 3.20/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.20/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.20/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.20/1.48  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.20/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.20/1.48  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.20/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.20/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.20/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.20/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.20/1.48  tff('#skF_6', type, '#skF_6': $i).
% 3.20/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.20/1.48  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.20/1.49  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.20/1.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.20/1.49  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.20/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.49  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.20/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.20/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.20/1.49  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.20/1.49  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.20/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.20/1.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.20/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.20/1.49  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.20/1.49  
% 3.20/1.49  tff(f_150, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 3.20/1.49  tff(f_121, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 3.20/1.49  tff(f_62, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.20/1.49  tff(f_68, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.20/1.49  tff(f_54, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.20/1.49  tff(f_42, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.20/1.49  tff(f_60, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.20/1.49  tff(c_82, plain, (k10_relat_1(k7_relat_1('#skF_4', '#skF_5'), '#skF_6')!=k10_relat_1('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.20/1.49  tff(c_88, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.20/1.49  tff(c_1349, plain, (![A_147, C_148, B_149]: (k3_xboole_0(A_147, k10_relat_1(C_148, B_149))=k10_relat_1(k7_relat_1(C_148, A_147), B_149) | ~v1_relat_1(C_148))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.20/1.49  tff(c_30, plain, (![B_21, A_20]: (k2_tarski(B_21, A_20)=k2_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.20/1.49  tff(c_329, plain, (![A_91, B_92]: (k1_setfam_1(k2_tarski(A_91, B_92))=k3_xboole_0(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.20/1.49  tff(c_344, plain, (![B_93, A_94]: (k1_setfam_1(k2_tarski(B_93, A_94))=k3_xboole_0(A_94, B_93))), inference(superposition, [status(thm), theory('equality')], [c_30, c_329])).
% 3.20/1.49  tff(c_36, plain, (![A_26, B_27]: (k1_setfam_1(k2_tarski(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.20/1.49  tff(c_350, plain, (![B_93, A_94]: (k3_xboole_0(B_93, A_94)=k3_xboole_0(A_94, B_93))), inference(superposition, [status(thm), theory('equality')], [c_344, c_36])).
% 3.20/1.49  tff(c_24, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.20/1.49  tff(c_84, plain, (r1_tarski(k10_relat_1('#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.20/1.49  tff(c_225, plain, (![A_86, B_87]: (k4_xboole_0(A_86, B_87)=k1_xboole_0 | ~r1_tarski(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.20/1.49  tff(c_243, plain, (k4_xboole_0(k10_relat_1('#skF_4', '#skF_6'), '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_84, c_225])).
% 3.20/1.49  tff(c_437, plain, (![A_103, B_104]: (k4_xboole_0(A_103, k4_xboole_0(A_103, B_104))=k3_xboole_0(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.20/1.49  tff(c_465, plain, (k4_xboole_0(k10_relat_1('#skF_4', '#skF_6'), k1_xboole_0)=k3_xboole_0(k10_relat_1('#skF_4', '#skF_6'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_243, c_437])).
% 3.20/1.49  tff(c_482, plain, (k3_xboole_0('#skF_5', k10_relat_1('#skF_4', '#skF_6'))=k10_relat_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_350, c_24, c_465])).
% 3.20/1.49  tff(c_1383, plain, (k10_relat_1(k7_relat_1('#skF_4', '#skF_5'), '#skF_6')=k10_relat_1('#skF_4', '#skF_6') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1349, c_482])).
% 3.20/1.49  tff(c_1429, plain, (k10_relat_1(k7_relat_1('#skF_4', '#skF_5'), '#skF_6')=k10_relat_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1383])).
% 3.20/1.49  tff(c_1431, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_1429])).
% 3.20/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.49  
% 3.20/1.49  Inference rules
% 3.20/1.49  ----------------------
% 3.20/1.49  #Ref     : 0
% 3.20/1.49  #Sup     : 330
% 3.20/1.49  #Fact    : 0
% 3.20/1.49  #Define  : 0
% 3.20/1.49  #Split   : 1
% 3.20/1.49  #Chain   : 0
% 3.20/1.49  #Close   : 0
% 3.20/1.49  
% 3.20/1.49  Ordering : KBO
% 3.20/1.49  
% 3.20/1.49  Simplification rules
% 3.20/1.49  ----------------------
% 3.20/1.49  #Subsume      : 26
% 3.20/1.49  #Demod        : 116
% 3.20/1.49  #Tautology    : 220
% 3.20/1.49  #SimpNegUnit  : 1
% 3.20/1.49  #BackRed      : 0
% 3.20/1.49  
% 3.20/1.49  #Partial instantiations: 0
% 3.20/1.49  #Strategies tried      : 1
% 3.20/1.49  
% 3.20/1.49  Timing (in seconds)
% 3.20/1.49  ----------------------
% 3.20/1.50  Preprocessing        : 0.35
% 3.20/1.50  Parsing              : 0.18
% 3.20/1.50  CNF conversion       : 0.03
% 3.20/1.50  Main loop            : 0.37
% 3.20/1.50  Inferencing          : 0.12
% 3.20/1.50  Reduction            : 0.14
% 3.20/1.50  Demodulation         : 0.10
% 3.20/1.50  BG Simplification    : 0.02
% 3.20/1.50  Subsumption          : 0.07
% 3.20/1.50  Abstraction          : 0.02
% 3.20/1.50  MUC search           : 0.00
% 3.20/1.50  Cooper               : 0.00
% 3.20/1.50  Total                : 0.75
% 3.20/1.50  Index Insertion      : 0.00
% 3.20/1.50  Index Deletion       : 0.00
% 3.20/1.50  Index Matching       : 0.00
% 3.20/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
