%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:23 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :   52 (  55 expanded)
%              Number of leaves         :   34 (  37 expanded)
%              Depth                    :    7
%              Number of atoms          :   33 (  42 expanded)
%              Number of equality atoms :   22 (  25 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(f_125,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_56,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_62,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_48,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_70,plain,(
    k10_relat_1(k7_relat_1('#skF_4','#skF_5'),'#skF_6') != k10_relat_1('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_76,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1154,plain,(
    ! [A_128,C_129,B_130] :
      ( k3_xboole_0(A_128,k10_relat_1(C_129,B_130)) = k10_relat_1(k7_relat_1(C_129,A_128),B_130)
      | ~ v1_relat_1(C_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_24,plain,(
    ! [B_19,A_18] : k2_tarski(B_19,A_18) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_195,plain,(
    ! [A_72,B_73] : k1_setfam_1(k2_tarski(A_72,B_73)) = k3_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_330,plain,(
    ! [B_83,A_84] : k1_setfam_1(k2_tarski(B_83,A_84)) = k3_xboole_0(A_84,B_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_195])).

tff(c_30,plain,(
    ! [A_24,B_25] : k1_setfam_1(k2_tarski(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_336,plain,(
    ! [B_83,A_84] : k3_xboole_0(B_83,A_84) = k3_xboole_0(A_84,B_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_30])).

tff(c_18,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_72,plain,(
    r1_tarski(k10_relat_1('#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_210,plain,(
    ! [A_74,B_75] :
      ( k4_xboole_0(A_74,B_75) = k1_xboole_0
      | ~ r1_tarski(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_224,plain,(
    k4_xboole_0(k10_relat_1('#skF_4','#skF_6'),'#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_72,c_210])).

tff(c_411,plain,(
    ! [A_91,B_92] : k4_xboole_0(A_91,k4_xboole_0(A_91,B_92)) = k3_xboole_0(A_91,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_439,plain,(
    k4_xboole_0(k10_relat_1('#skF_4','#skF_6'),k1_xboole_0) = k3_xboole_0(k10_relat_1('#skF_4','#skF_6'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_411])).

tff(c_456,plain,(
    k3_xboole_0('#skF_5',k10_relat_1('#skF_4','#skF_6')) = k10_relat_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_18,c_439])).

tff(c_1178,plain,
    ( k10_relat_1(k7_relat_1('#skF_4','#skF_5'),'#skF_6') = k10_relat_1('#skF_4','#skF_6')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1154,c_456])).

tff(c_1226,plain,(
    k10_relat_1(k7_relat_1('#skF_4','#skF_5'),'#skF_6') = k10_relat_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1178])).

tff(c_1228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1226])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:43:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.55/2.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/2.04  
% 3.55/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/2.05  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.55/2.05  
% 3.55/2.05  %Foreground sorts:
% 3.55/2.05  
% 3.55/2.05  
% 3.55/2.05  %Background operators:
% 3.55/2.05  
% 3.55/2.05  
% 3.55/2.05  %Foreground operators:
% 3.55/2.05  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.55/2.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.55/2.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.55/2.05  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.55/2.05  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.55/2.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.55/2.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.55/2.05  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.55/2.05  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.55/2.05  tff('#skF_5', type, '#skF_5': $i).
% 3.55/2.05  tff('#skF_6', type, '#skF_6': $i).
% 3.55/2.05  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.55/2.05  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.55/2.05  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.55/2.05  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.55/2.05  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.55/2.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.55/2.05  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.55/2.05  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.55/2.05  tff('#skF_4', type, '#skF_4': $i).
% 3.55/2.05  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.55/2.05  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.55/2.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.55/2.05  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.55/2.05  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.55/2.05  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.55/2.05  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.55/2.05  
% 3.55/2.06  tff(f_125, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 3.55/2.06  tff(f_102, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 3.55/2.06  tff(f_56, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.55/2.06  tff(f_62, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.55/2.06  tff(f_48, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.55/2.06  tff(f_36, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.55/2.06  tff(f_54, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.55/2.06  tff(c_70, plain, (k10_relat_1(k7_relat_1('#skF_4', '#skF_5'), '#skF_6')!=k10_relat_1('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.55/2.06  tff(c_76, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.55/2.06  tff(c_1154, plain, (![A_128, C_129, B_130]: (k3_xboole_0(A_128, k10_relat_1(C_129, B_130))=k10_relat_1(k7_relat_1(C_129, A_128), B_130) | ~v1_relat_1(C_129))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.55/2.06  tff(c_24, plain, (![B_19, A_18]: (k2_tarski(B_19, A_18)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.55/2.06  tff(c_195, plain, (![A_72, B_73]: (k1_setfam_1(k2_tarski(A_72, B_73))=k3_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.55/2.06  tff(c_330, plain, (![B_83, A_84]: (k1_setfam_1(k2_tarski(B_83, A_84))=k3_xboole_0(A_84, B_83))), inference(superposition, [status(thm), theory('equality')], [c_24, c_195])).
% 3.55/2.06  tff(c_30, plain, (![A_24, B_25]: (k1_setfam_1(k2_tarski(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.55/2.06  tff(c_336, plain, (![B_83, A_84]: (k3_xboole_0(B_83, A_84)=k3_xboole_0(A_84, B_83))), inference(superposition, [status(thm), theory('equality')], [c_330, c_30])).
% 3.55/2.06  tff(c_18, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.55/2.06  tff(c_72, plain, (r1_tarski(k10_relat_1('#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.55/2.06  tff(c_210, plain, (![A_74, B_75]: (k4_xboole_0(A_74, B_75)=k1_xboole_0 | ~r1_tarski(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.55/2.06  tff(c_224, plain, (k4_xboole_0(k10_relat_1('#skF_4', '#skF_6'), '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_72, c_210])).
% 3.55/2.06  tff(c_411, plain, (![A_91, B_92]: (k4_xboole_0(A_91, k4_xboole_0(A_91, B_92))=k3_xboole_0(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.55/2.06  tff(c_439, plain, (k4_xboole_0(k10_relat_1('#skF_4', '#skF_6'), k1_xboole_0)=k3_xboole_0(k10_relat_1('#skF_4', '#skF_6'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_224, c_411])).
% 3.55/2.06  tff(c_456, plain, (k3_xboole_0('#skF_5', k10_relat_1('#skF_4', '#skF_6'))=k10_relat_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_336, c_18, c_439])).
% 3.55/2.06  tff(c_1178, plain, (k10_relat_1(k7_relat_1('#skF_4', '#skF_5'), '#skF_6')=k10_relat_1('#skF_4', '#skF_6') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1154, c_456])).
% 3.55/2.06  tff(c_1226, plain, (k10_relat_1(k7_relat_1('#skF_4', '#skF_5'), '#skF_6')=k10_relat_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1178])).
% 3.55/2.06  tff(c_1228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_1226])).
% 3.55/2.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/2.06  
% 3.55/2.06  Inference rules
% 3.55/2.06  ----------------------
% 3.55/2.06  #Ref     : 0
% 3.55/2.06  #Sup     : 276
% 3.55/2.06  #Fact    : 0
% 3.55/2.06  #Define  : 0
% 3.55/2.06  #Split   : 1
% 3.55/2.06  #Chain   : 0
% 3.55/2.06  #Close   : 0
% 3.55/2.06  
% 3.55/2.06  Ordering : KBO
% 3.55/2.06  
% 3.55/2.06  Simplification rules
% 3.55/2.06  ----------------------
% 3.55/2.06  #Subsume      : 6
% 3.55/2.06  #Demod        : 115
% 3.55/2.06  #Tautology    : 196
% 3.55/2.06  #SimpNegUnit  : 1
% 3.55/2.06  #BackRed      : 0
% 3.55/2.06  
% 3.55/2.06  #Partial instantiations: 0
% 3.55/2.06  #Strategies tried      : 1
% 3.55/2.06  
% 3.55/2.06  Timing (in seconds)
% 3.55/2.06  ----------------------
% 3.55/2.07  Preprocessing        : 0.57
% 3.55/2.07  Parsing              : 0.29
% 3.55/2.07  CNF conversion       : 0.04
% 3.55/2.07  Main loop            : 0.58
% 3.55/2.07  Inferencing          : 0.20
% 3.55/2.07  Reduction            : 0.22
% 3.55/2.07  Demodulation         : 0.17
% 3.55/2.07  BG Simplification    : 0.04
% 3.55/2.07  Subsumption          : 0.09
% 3.55/2.07  Abstraction          : 0.03
% 3.55/2.07  MUC search           : 0.00
% 3.55/2.07  Cooper               : 0.00
% 3.55/2.07  Total                : 1.19
% 3.55/2.07  Index Insertion      : 0.00
% 3.55/2.07  Index Deletion       : 0.00
% 3.55/2.07  Index Matching       : 0.00
% 3.55/2.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
