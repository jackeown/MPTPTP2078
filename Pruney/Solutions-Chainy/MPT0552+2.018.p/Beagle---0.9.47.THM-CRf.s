%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:59 EST 2020

% Result     : Theorem 10.41s
% Output     : CNFRefutation 10.41s
% Verified   : 
% Statistics : Number of formulae       :   59 (  90 expanded)
%              Number of leaves         :   25 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   72 ( 128 expanded)
%              Number of equality atoms :   18 (  30 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_57,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k9_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_18,plain,(
    ! [B_16,A_15] : k2_tarski(B_16,A_15) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_117,plain,(
    ! [A_38,B_39] : k1_setfam_1(k2_tarski(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_141,plain,(
    ! [B_42,A_43] : k1_setfam_1(k2_tarski(B_42,A_43)) = k3_xboole_0(A_43,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_117])).

tff(c_24,plain,(
    ! [A_22,B_23] : k1_setfam_1(k2_tarski(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_147,plain,(
    ! [B_42,A_43] : k3_xboole_0(B_42,A_43) = k3_xboole_0(A_43,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_24])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [A_12,C_14,B_13] :
      ( r1_tarski(k2_xboole_0(A_12,C_14),B_13)
      | ~ r1_tarski(C_14,B_13)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    ! [A_10,B_11] : r1_tarski(A_10,k2_xboole_0(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_213,plain,(
    ! [B_48,A_49] :
      ( B_48 = A_49
      | ~ r1_tarski(B_48,A_49)
      | ~ r1_tarski(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_264,plain,(
    ! [A_58,B_59] :
      ( k2_xboole_0(A_58,B_59) = A_58
      | ~ r1_tarski(k2_xboole_0(A_58,B_59),A_58) ) ),
    inference(resolution,[status(thm)],[c_14,c_213])).

tff(c_268,plain,(
    ! [B_13,C_14] :
      ( k2_xboole_0(B_13,C_14) = B_13
      | ~ r1_tarski(C_14,B_13)
      | ~ r1_tarski(B_13,B_13) ) ),
    inference(resolution,[status(thm)],[c_16,c_264])).

tff(c_278,plain,(
    ! [B_60,C_61] :
      ( k2_xboole_0(B_60,C_61) = B_60
      | ~ r1_tarski(C_61,B_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_268])).

tff(c_300,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = A_5 ),
    inference(resolution,[status(thm)],[c_10,c_278])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10999,plain,(
    ! [C_234,A_235,B_236] :
      ( k2_xboole_0(k9_relat_1(C_234,A_235),k9_relat_1(C_234,B_236)) = k9_relat_1(C_234,k2_xboole_0(A_235,B_236))
      | ~ v1_relat_1(C_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_11450,plain,(
    ! [C_247,A_248,B_249] :
      ( r1_tarski(k9_relat_1(C_247,A_248),k9_relat_1(C_247,k2_xboole_0(A_248,B_249)))
      | ~ v1_relat_1(C_247) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10999,c_14])).

tff(c_15222,plain,(
    ! [C_313,A_314,B_315] :
      ( r1_tarski(k9_relat_1(C_313,A_314),k9_relat_1(C_313,k2_xboole_0(B_315,A_314)))
      | ~ v1_relat_1(C_313) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_11450])).

tff(c_20949,plain,(
    ! [C_374,A_375,B_376] :
      ( r1_tarski(k9_relat_1(C_374,k3_xboole_0(A_375,B_376)),k9_relat_1(C_374,A_375))
      | ~ v1_relat_1(C_374) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_15222])).

tff(c_21204,plain,(
    ! [C_380,A_381,B_382] :
      ( r1_tarski(k9_relat_1(C_380,k3_xboole_0(A_381,B_382)),k9_relat_1(C_380,B_382))
      | ~ v1_relat_1(C_380) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_20949])).

tff(c_608,plain,(
    ! [C_77,A_78,B_79] :
      ( k2_xboole_0(k9_relat_1(C_77,A_78),k9_relat_1(C_77,B_79)) = k9_relat_1(C_77,k2_xboole_0(A_78,B_79))
      | ~ v1_relat_1(C_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1185,plain,(
    ! [C_92,A_93,B_94] :
      ( r1_tarski(k9_relat_1(C_92,A_93),k9_relat_1(C_92,k2_xboole_0(A_93,B_94)))
      | ~ v1_relat_1(C_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_608,c_14])).

tff(c_4268,plain,(
    ! [C_154,A_155,B_156] :
      ( r1_tarski(k9_relat_1(C_154,A_155),k9_relat_1(C_154,k2_xboole_0(B_156,A_155)))
      | ~ v1_relat_1(C_154) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1185])).

tff(c_10727,plain,(
    ! [C_224,A_225,B_226] :
      ( r1_tarski(k9_relat_1(C_224,k3_xboole_0(A_225,B_226)),k9_relat_1(C_224,A_225))
      | ~ v1_relat_1(C_224) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_4268])).

tff(c_359,plain,(
    ! [A_65,B_66,C_67] :
      ( r1_tarski(A_65,k3_xboole_0(B_66,C_67))
      | ~ r1_tarski(A_65,C_67)
      | ~ r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_28,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_388,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_359,c_28])).

tff(c_434,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_388])).

tff(c_10736,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10727,c_434])).

tff(c_10823,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_10736])).

tff(c_10824,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_388])).

tff(c_21216,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_21204,c_10824])).

tff(c_21308,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_21216])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:00:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.41/3.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.41/3.76  
% 10.41/3.76  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.41/3.76  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 10.41/3.76  
% 10.41/3.76  %Foreground sorts:
% 10.41/3.76  
% 10.41/3.76  
% 10.41/3.76  %Background operators:
% 10.41/3.76  
% 10.41/3.76  
% 10.41/3.76  %Foreground operators:
% 10.41/3.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.41/3.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.41/3.76  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.41/3.76  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.41/3.76  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.41/3.76  tff('#skF_2', type, '#skF_2': $i).
% 10.41/3.76  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 10.41/3.76  tff('#skF_3', type, '#skF_3': $i).
% 10.41/3.76  tff('#skF_1', type, '#skF_1': $i).
% 10.41/3.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.41/3.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.41/3.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.41/3.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.41/3.76  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.41/3.76  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.41/3.76  
% 10.41/3.77  tff(f_66, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_relat_1)).
% 10.41/3.77  tff(f_51, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 10.41/3.77  tff(f_57, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 10.41/3.77  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 10.41/3.77  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.41/3.77  tff(f_49, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 10.41/3.77  tff(f_43, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 10.41/3.77  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 10.41/3.77  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (k9_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t153_relat_1)).
% 10.41/3.77  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 10.41/3.77  tff(c_30, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.41/3.77  tff(c_18, plain, (![B_16, A_15]: (k2_tarski(B_16, A_15)=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.41/3.77  tff(c_117, plain, (![A_38, B_39]: (k1_setfam_1(k2_tarski(A_38, B_39))=k3_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.41/3.77  tff(c_141, plain, (![B_42, A_43]: (k1_setfam_1(k2_tarski(B_42, A_43))=k3_xboole_0(A_43, B_42))), inference(superposition, [status(thm), theory('equality')], [c_18, c_117])).
% 10.41/3.77  tff(c_24, plain, (![A_22, B_23]: (k1_setfam_1(k2_tarski(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.41/3.77  tff(c_147, plain, (![B_42, A_43]: (k3_xboole_0(B_42, A_43)=k3_xboole_0(A_43, B_42))), inference(superposition, [status(thm), theory('equality')], [c_141, c_24])).
% 10.41/3.77  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.41/3.77  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.41/3.77  tff(c_16, plain, (![A_12, C_14, B_13]: (r1_tarski(k2_xboole_0(A_12, C_14), B_13) | ~r1_tarski(C_14, B_13) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.41/3.77  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(A_10, k2_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.41/3.77  tff(c_213, plain, (![B_48, A_49]: (B_48=A_49 | ~r1_tarski(B_48, A_49) | ~r1_tarski(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.41/3.77  tff(c_264, plain, (![A_58, B_59]: (k2_xboole_0(A_58, B_59)=A_58 | ~r1_tarski(k2_xboole_0(A_58, B_59), A_58))), inference(resolution, [status(thm)], [c_14, c_213])).
% 10.41/3.77  tff(c_268, plain, (![B_13, C_14]: (k2_xboole_0(B_13, C_14)=B_13 | ~r1_tarski(C_14, B_13) | ~r1_tarski(B_13, B_13))), inference(resolution, [status(thm)], [c_16, c_264])).
% 10.41/3.77  tff(c_278, plain, (![B_60, C_61]: (k2_xboole_0(B_60, C_61)=B_60 | ~r1_tarski(C_61, B_60))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_268])).
% 10.41/3.77  tff(c_300, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k3_xboole_0(A_5, B_6))=A_5)), inference(resolution, [status(thm)], [c_10, c_278])).
% 10.41/3.77  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.41/3.77  tff(c_10999, plain, (![C_234, A_235, B_236]: (k2_xboole_0(k9_relat_1(C_234, A_235), k9_relat_1(C_234, B_236))=k9_relat_1(C_234, k2_xboole_0(A_235, B_236)) | ~v1_relat_1(C_234))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.41/3.77  tff(c_11450, plain, (![C_247, A_248, B_249]: (r1_tarski(k9_relat_1(C_247, A_248), k9_relat_1(C_247, k2_xboole_0(A_248, B_249))) | ~v1_relat_1(C_247))), inference(superposition, [status(thm), theory('equality')], [c_10999, c_14])).
% 10.41/3.77  tff(c_15222, plain, (![C_313, A_314, B_315]: (r1_tarski(k9_relat_1(C_313, A_314), k9_relat_1(C_313, k2_xboole_0(B_315, A_314))) | ~v1_relat_1(C_313))), inference(superposition, [status(thm), theory('equality')], [c_2, c_11450])).
% 10.41/3.77  tff(c_20949, plain, (![C_374, A_375, B_376]: (r1_tarski(k9_relat_1(C_374, k3_xboole_0(A_375, B_376)), k9_relat_1(C_374, A_375)) | ~v1_relat_1(C_374))), inference(superposition, [status(thm), theory('equality')], [c_300, c_15222])).
% 10.41/3.77  tff(c_21204, plain, (![C_380, A_381, B_382]: (r1_tarski(k9_relat_1(C_380, k3_xboole_0(A_381, B_382)), k9_relat_1(C_380, B_382)) | ~v1_relat_1(C_380))), inference(superposition, [status(thm), theory('equality')], [c_147, c_20949])).
% 10.41/3.77  tff(c_608, plain, (![C_77, A_78, B_79]: (k2_xboole_0(k9_relat_1(C_77, A_78), k9_relat_1(C_77, B_79))=k9_relat_1(C_77, k2_xboole_0(A_78, B_79)) | ~v1_relat_1(C_77))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.41/3.77  tff(c_1185, plain, (![C_92, A_93, B_94]: (r1_tarski(k9_relat_1(C_92, A_93), k9_relat_1(C_92, k2_xboole_0(A_93, B_94))) | ~v1_relat_1(C_92))), inference(superposition, [status(thm), theory('equality')], [c_608, c_14])).
% 10.41/3.77  tff(c_4268, plain, (![C_154, A_155, B_156]: (r1_tarski(k9_relat_1(C_154, A_155), k9_relat_1(C_154, k2_xboole_0(B_156, A_155))) | ~v1_relat_1(C_154))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1185])).
% 10.41/3.77  tff(c_10727, plain, (![C_224, A_225, B_226]: (r1_tarski(k9_relat_1(C_224, k3_xboole_0(A_225, B_226)), k9_relat_1(C_224, A_225)) | ~v1_relat_1(C_224))), inference(superposition, [status(thm), theory('equality')], [c_300, c_4268])).
% 10.41/3.77  tff(c_359, plain, (![A_65, B_66, C_67]: (r1_tarski(A_65, k3_xboole_0(B_66, C_67)) | ~r1_tarski(A_65, C_67) | ~r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.41/3.77  tff(c_28, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.41/3.77  tff(c_388, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_359, c_28])).
% 10.41/3.77  tff(c_434, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_388])).
% 10.41/3.77  tff(c_10736, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10727, c_434])).
% 10.41/3.77  tff(c_10823, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_10736])).
% 10.41/3.77  tff(c_10824, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_388])).
% 10.41/3.77  tff(c_21216, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_21204, c_10824])).
% 10.41/3.77  tff(c_21308, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_21216])).
% 10.41/3.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.41/3.77  
% 10.41/3.77  Inference rules
% 10.41/3.77  ----------------------
% 10.41/3.77  #Ref     : 0
% 10.41/3.77  #Sup     : 5309
% 10.41/3.77  #Fact    : 0
% 10.41/3.77  #Define  : 0
% 10.41/3.77  #Split   : 2
% 10.41/3.77  #Chain   : 0
% 10.41/3.77  #Close   : 0
% 10.41/3.77  
% 10.41/3.77  Ordering : KBO
% 10.41/3.77  
% 10.41/3.77  Simplification rules
% 10.41/3.77  ----------------------
% 10.41/3.77  #Subsume      : 1149
% 10.41/3.77  #Demod        : 8059
% 10.41/3.77  #Tautology    : 3206
% 10.41/3.77  #SimpNegUnit  : 0
% 10.41/3.77  #BackRed      : 0
% 10.41/3.77  
% 10.41/3.77  #Partial instantiations: 0
% 10.41/3.77  #Strategies tried      : 1
% 10.41/3.77  
% 10.41/3.77  Timing (in seconds)
% 10.41/3.77  ----------------------
% 10.41/3.78  Preprocessing        : 0.29
% 10.41/3.78  Parsing              : 0.16
% 10.41/3.78  CNF conversion       : 0.02
% 10.41/3.78  Main loop            : 2.71
% 10.41/3.78  Inferencing          : 0.61
% 10.41/3.78  Reduction            : 1.54
% 10.41/3.78  Demodulation         : 1.38
% 10.41/3.78  BG Simplification    : 0.06
% 10.41/3.78  Subsumption          : 0.38
% 10.41/3.78  Abstraction          : 0.15
% 10.41/3.78  MUC search           : 0.00
% 10.41/3.78  Cooper               : 0.00
% 10.41/3.78  Total                : 3.03
% 10.41/3.78  Index Insertion      : 0.00
% 10.41/3.78  Index Deletion       : 0.00
% 10.41/3.78  Index Matching       : 0.00
% 10.41/3.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
