%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:50 EST 2020

% Result     : Theorem 4.02s
% Output     : CNFRefutation 4.02s
% Verified   : 
% Statistics : Number of formulae       :   58 (  89 expanded)
%              Number of leaves         :   29 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :   55 ( 105 expanded)
%              Number of equality atoms :   25 (  42 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_44,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_52,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_66,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

tff(c_54,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_26,plain,(
    ! [A_12] : k2_xboole_0(A_12,A_12) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_40,plain,(
    ! [A_22,B_23] : r1_tarski(A_22,k2_xboole_0(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_388,plain,(
    ! [A_78,B_79,C_80] :
      ( r1_tarski(k4_xboole_0(A_78,B_79),C_80)
      | ~ r1_tarski(A_78,k2_xboole_0(B_79,C_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_34,plain,(
    ! [A_16] : r1_tarski(k1_xboole_0,A_16) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_260,plain,(
    ! [B_62,A_63] :
      ( B_62 = A_63
      | ~ r1_tarski(B_62,A_63)
      | ~ r1_tarski(A_63,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_286,plain,(
    ! [A_16] :
      ( k1_xboole_0 = A_16
      | ~ r1_tarski(A_16,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_34,c_260])).

tff(c_402,plain,(
    ! [A_81,B_82] :
      ( k4_xboole_0(A_81,B_82) = k1_xboole_0
      | ~ r1_tarski(A_81,k2_xboole_0(B_82,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_388,c_286])).

tff(c_458,plain,(
    ! [A_83] : k4_xboole_0(A_83,A_83) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_402])).

tff(c_36,plain,(
    ! [A_17,B_18] : k2_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_475,plain,(
    ! [A_83] : k2_xboole_0(A_83,k1_xboole_0) = k2_xboole_0(A_83,A_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_36])).

tff(c_486,plain,(
    ! [A_83] : k2_xboole_0(A_83,k1_xboole_0) = A_83 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_475])).

tff(c_42,plain,(
    ! [B_25,A_24] : k2_tarski(B_25,A_24) = k2_tarski(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_105,plain,(
    ! [A_40,B_41] : k3_tarski(k2_tarski(A_40,B_41)) = k2_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_129,plain,(
    ! [A_44,B_45] : k3_tarski(k2_tarski(A_44,B_45)) = k2_xboole_0(B_45,A_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_105])).

tff(c_46,plain,(
    ! [A_28,B_29] : k3_tarski(k2_tarski(A_28,B_29)) = k2_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_135,plain,(
    ! [B_45,A_44] : k2_xboole_0(B_45,A_44) = k2_xboole_0(A_44,B_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_46])).

tff(c_52,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_398,plain,(
    ! [A_78,B_79] :
      ( k4_xboole_0(A_78,B_79) = k1_xboole_0
      | ~ r1_tarski(A_78,k2_xboole_0(B_79,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_388,c_286])).

tff(c_892,plain,(
    ! [A_109,B_110] :
      ( k4_xboole_0(A_109,B_110) = k1_xboole_0
      | ~ r1_tarski(A_109,B_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_486,c_398])).

tff(c_926,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_892])).

tff(c_945,plain,(
    k2_xboole_0('#skF_5',k1_xboole_0) = k2_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_926,c_36])).

tff(c_954,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_486,c_135,c_945])).

tff(c_690,plain,(
    ! [C_90,A_91,B_92] :
      ( k2_xboole_0(k10_relat_1(C_90,A_91),k10_relat_1(C_90,B_92)) = k10_relat_1(C_90,k2_xboole_0(A_91,B_92))
      | ~ v1_relat_1(C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2751,plain,(
    ! [C_152,A_153,B_154] :
      ( r1_tarski(k10_relat_1(C_152,A_153),k10_relat_1(C_152,k2_xboole_0(A_153,B_154)))
      | ~ v1_relat_1(C_152) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_690,c_40])).

tff(c_3107,plain,(
    ! [C_165] :
      ( r1_tarski(k10_relat_1(C_165,'#skF_4'),k10_relat_1(C_165,'#skF_5'))
      | ~ v1_relat_1(C_165) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_954,c_2751])).

tff(c_50,plain,(
    ~ r1_tarski(k10_relat_1('#skF_6','#skF_4'),k10_relat_1('#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_3115,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_3107,c_50])).

tff(c_3121,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3115])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:14:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.02/1.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.02/1.75  
% 4.02/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.02/1.75  %$ r2_hidden > r1_tarski > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 4.02/1.75  
% 4.02/1.75  %Foreground sorts:
% 4.02/1.75  
% 4.02/1.75  
% 4.02/1.75  %Background operators:
% 4.02/1.75  
% 4.02/1.75  
% 4.02/1.75  %Foreground operators:
% 4.02/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.02/1.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.02/1.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.02/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.02/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.02/1.75  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.02/1.75  tff('#skF_5', type, '#skF_5': $i).
% 4.02/1.75  tff('#skF_6', type, '#skF_6': $i).
% 4.02/1.75  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.02/1.75  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.02/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.02/1.75  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.02/1.75  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.02/1.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.02/1.75  tff('#skF_4', type, '#skF_4': $i).
% 4.02/1.75  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.02/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.02/1.75  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.02/1.75  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.02/1.75  
% 4.02/1.77  tff(f_77, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_relat_1)).
% 4.02/1.77  tff(f_44, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 4.02/1.77  tff(f_60, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.02/1.77  tff(f_58, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 4.02/1.77  tff(f_52, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.02/1.77  tff(f_50, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.02/1.77  tff(f_54, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.02/1.77  tff(f_62, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.02/1.77  tff(f_66, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.02/1.77  tff(f_70, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_relat_1)).
% 4.02/1.77  tff(c_54, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.02/1.77  tff(c_26, plain, (![A_12]: (k2_xboole_0(A_12, A_12)=A_12)), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.02/1.77  tff(c_40, plain, (![A_22, B_23]: (r1_tarski(A_22, k2_xboole_0(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.02/1.77  tff(c_388, plain, (![A_78, B_79, C_80]: (r1_tarski(k4_xboole_0(A_78, B_79), C_80) | ~r1_tarski(A_78, k2_xboole_0(B_79, C_80)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.02/1.77  tff(c_34, plain, (![A_16]: (r1_tarski(k1_xboole_0, A_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.02/1.77  tff(c_260, plain, (![B_62, A_63]: (B_62=A_63 | ~r1_tarski(B_62, A_63) | ~r1_tarski(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.02/1.77  tff(c_286, plain, (![A_16]: (k1_xboole_0=A_16 | ~r1_tarski(A_16, k1_xboole_0))), inference(resolution, [status(thm)], [c_34, c_260])).
% 4.02/1.77  tff(c_402, plain, (![A_81, B_82]: (k4_xboole_0(A_81, B_82)=k1_xboole_0 | ~r1_tarski(A_81, k2_xboole_0(B_82, k1_xboole_0)))), inference(resolution, [status(thm)], [c_388, c_286])).
% 4.02/1.77  tff(c_458, plain, (![A_83]: (k4_xboole_0(A_83, A_83)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_402])).
% 4.02/1.77  tff(c_36, plain, (![A_17, B_18]: (k2_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.02/1.77  tff(c_475, plain, (![A_83]: (k2_xboole_0(A_83, k1_xboole_0)=k2_xboole_0(A_83, A_83))), inference(superposition, [status(thm), theory('equality')], [c_458, c_36])).
% 4.02/1.77  tff(c_486, plain, (![A_83]: (k2_xboole_0(A_83, k1_xboole_0)=A_83)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_475])).
% 4.02/1.77  tff(c_42, plain, (![B_25, A_24]: (k2_tarski(B_25, A_24)=k2_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.02/1.77  tff(c_105, plain, (![A_40, B_41]: (k3_tarski(k2_tarski(A_40, B_41))=k2_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.02/1.77  tff(c_129, plain, (![A_44, B_45]: (k3_tarski(k2_tarski(A_44, B_45))=k2_xboole_0(B_45, A_44))), inference(superposition, [status(thm), theory('equality')], [c_42, c_105])).
% 4.02/1.77  tff(c_46, plain, (![A_28, B_29]: (k3_tarski(k2_tarski(A_28, B_29))=k2_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.02/1.77  tff(c_135, plain, (![B_45, A_44]: (k2_xboole_0(B_45, A_44)=k2_xboole_0(A_44, B_45))), inference(superposition, [status(thm), theory('equality')], [c_129, c_46])).
% 4.02/1.77  tff(c_52, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.02/1.77  tff(c_398, plain, (![A_78, B_79]: (k4_xboole_0(A_78, B_79)=k1_xboole_0 | ~r1_tarski(A_78, k2_xboole_0(B_79, k1_xboole_0)))), inference(resolution, [status(thm)], [c_388, c_286])).
% 4.02/1.77  tff(c_892, plain, (![A_109, B_110]: (k4_xboole_0(A_109, B_110)=k1_xboole_0 | ~r1_tarski(A_109, B_110))), inference(demodulation, [status(thm), theory('equality')], [c_486, c_398])).
% 4.02/1.77  tff(c_926, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_892])).
% 4.02/1.77  tff(c_945, plain, (k2_xboole_0('#skF_5', k1_xboole_0)=k2_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_926, c_36])).
% 4.02/1.77  tff(c_954, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_486, c_135, c_945])).
% 4.02/1.77  tff(c_690, plain, (![C_90, A_91, B_92]: (k2_xboole_0(k10_relat_1(C_90, A_91), k10_relat_1(C_90, B_92))=k10_relat_1(C_90, k2_xboole_0(A_91, B_92)) | ~v1_relat_1(C_90))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.02/1.77  tff(c_2751, plain, (![C_152, A_153, B_154]: (r1_tarski(k10_relat_1(C_152, A_153), k10_relat_1(C_152, k2_xboole_0(A_153, B_154))) | ~v1_relat_1(C_152))), inference(superposition, [status(thm), theory('equality')], [c_690, c_40])).
% 4.02/1.77  tff(c_3107, plain, (![C_165]: (r1_tarski(k10_relat_1(C_165, '#skF_4'), k10_relat_1(C_165, '#skF_5')) | ~v1_relat_1(C_165))), inference(superposition, [status(thm), theory('equality')], [c_954, c_2751])).
% 4.02/1.77  tff(c_50, plain, (~r1_tarski(k10_relat_1('#skF_6', '#skF_4'), k10_relat_1('#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.02/1.77  tff(c_3115, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_3107, c_50])).
% 4.02/1.77  tff(c_3121, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_3115])).
% 4.02/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.02/1.77  
% 4.02/1.77  Inference rules
% 4.02/1.77  ----------------------
% 4.02/1.77  #Ref     : 0
% 4.02/1.77  #Sup     : 752
% 4.02/1.77  #Fact    : 2
% 4.02/1.77  #Define  : 0
% 4.02/1.77  #Split   : 1
% 4.02/1.77  #Chain   : 0
% 4.02/1.77  #Close   : 0
% 4.02/1.77  
% 4.02/1.77  Ordering : KBO
% 4.02/1.77  
% 4.02/1.77  Simplification rules
% 4.02/1.77  ----------------------
% 4.02/1.77  #Subsume      : 55
% 4.02/1.77  #Demod        : 664
% 4.02/1.77  #Tautology    : 481
% 4.02/1.77  #SimpNegUnit  : 0
% 4.02/1.77  #BackRed      : 2
% 4.02/1.77  
% 4.02/1.77  #Partial instantiations: 0
% 4.02/1.77  #Strategies tried      : 1
% 4.02/1.77  
% 4.02/1.77  Timing (in seconds)
% 4.02/1.77  ----------------------
% 4.02/1.77  Preprocessing        : 0.33
% 4.02/1.77  Parsing              : 0.17
% 4.02/1.77  CNF conversion       : 0.02
% 4.02/1.77  Main loop            : 0.67
% 4.02/1.77  Inferencing          : 0.21
% 4.02/1.77  Reduction            : 0.27
% 4.02/1.77  Demodulation         : 0.22
% 4.02/1.77  BG Simplification    : 0.03
% 4.02/1.77  Subsumption          : 0.11
% 4.02/1.77  Abstraction          : 0.04
% 4.02/1.77  MUC search           : 0.00
% 4.02/1.77  Cooper               : 0.00
% 4.02/1.77  Total                : 1.02
% 4.02/1.77  Index Insertion      : 0.00
% 4.02/1.77  Index Deletion       : 0.00
% 4.02/1.77  Index Matching       : 0.00
% 4.02/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
