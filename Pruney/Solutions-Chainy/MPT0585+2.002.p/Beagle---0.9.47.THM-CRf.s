%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:00 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   49 (  71 expanded)
%              Number of leaves         :   21 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :   70 ( 107 expanded)
%              Number of equality atoms :   30 (  48 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_65,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => k7_relat_1(A,k1_relat_1(B)) = k7_relat_1(A,k1_relat_1(k7_relat_1(B,k1_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_62,plain,(
    ! [A_22,B_23] : k1_setfam_1(k2_tarski(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_96,plain,(
    ! [A_29,B_30] : k1_setfam_1(k2_tarski(A_29,B_30)) = k3_xboole_0(B_30,A_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_62])).

tff(c_12,plain,(
    ! [A_7,B_8] : k1_setfam_1(k2_tarski(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_102,plain,(
    ! [B_30,A_29] : k3_xboole_0(B_30,A_29) = k3_xboole_0(A_29,B_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_12])).

tff(c_91,plain,(
    ! [B_27,A_28] :
      ( r1_tarski(k7_relat_1(B_27,A_28),B_27)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_95,plain,(
    ! [B_27,A_28] :
      ( k3_xboole_0(k7_relat_1(B_27,A_28),B_27) = k7_relat_1(B_27,A_28)
      | ~ v1_relat_1(B_27) ) ),
    inference(resolution,[status(thm)],[c_91,c_8])).

tff(c_279,plain,(
    ! [B_27,A_28] :
      ( k3_xboole_0(B_27,k7_relat_1(B_27,A_28)) = k7_relat_1(B_27,A_28)
      | ~ v1_relat_1(B_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_95])).

tff(c_18,plain,(
    ! [B_15,A_14] :
      ( k3_xboole_0(k1_relat_1(B_15),A_14) = k1_relat_1(k7_relat_1(B_15,A_14))
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_163,plain,(
    ! [B_35,A_36] :
      ( k7_relat_1(B_35,A_36) = B_35
      | ~ r1_tarski(k1_relat_1(B_35),A_36)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_168,plain,(
    ! [B_35] :
      ( k7_relat_1(B_35,k1_relat_1(B_35)) = B_35
      | ~ v1_relat_1(B_35) ) ),
    inference(resolution,[status(thm)],[c_6,c_163])).

tff(c_241,plain,(
    ! [C_41,A_42,B_43] :
      ( k3_xboole_0(k7_relat_1(C_41,A_42),k7_relat_1(C_41,B_43)) = k7_relat_1(C_41,k3_xboole_0(A_42,B_43))
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_611,plain,(
    ! [B_58,B_59] :
      ( k7_relat_1(B_58,k3_xboole_0(k1_relat_1(B_58),B_59)) = k3_xboole_0(B_58,k7_relat_1(B_58,B_59))
      | ~ v1_relat_1(B_58)
      | ~ v1_relat_1(B_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_241])).

tff(c_1087,plain,(
    ! [B_72,A_73] :
      ( k7_relat_1(B_72,k1_relat_1(k7_relat_1(B_72,A_73))) = k3_xboole_0(B_72,k7_relat_1(B_72,A_73))
      | ~ v1_relat_1(B_72)
      | ~ v1_relat_1(B_72)
      | ~ v1_relat_1(B_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_611])).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_169,plain,(
    ! [B_37,A_38] :
      ( k3_xboole_0(k1_relat_1(B_37),A_38) = k1_relat_1(k7_relat_1(B_37,A_38))
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_301,plain,(
    ! [A_46,B_47] :
      ( k3_xboole_0(A_46,k1_relat_1(B_47)) = k1_relat_1(k7_relat_1(B_47,A_46))
      | ~ v1_relat_1(B_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_102])).

tff(c_393,plain,(
    ! [B_54,B_53] :
      ( k1_relat_1(k7_relat_1(B_54,k1_relat_1(B_53))) = k1_relat_1(k7_relat_1(B_53,k1_relat_1(B_54)))
      | ~ v1_relat_1(B_53)
      | ~ v1_relat_1(B_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_301])).

tff(c_22,plain,(
    k7_relat_1('#skF_1',k1_relat_1(k7_relat_1('#skF_2',k1_relat_1('#skF_1')))) != k7_relat_1('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_450,plain,
    ( k7_relat_1('#skF_1',k1_relat_1(k7_relat_1('#skF_1',k1_relat_1('#skF_2')))) != k7_relat_1('#skF_1',k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_22])).

tff(c_489,plain,(
    k7_relat_1('#skF_1',k1_relat_1(k7_relat_1('#skF_1',k1_relat_1('#skF_2')))) != k7_relat_1('#skF_1',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_450])).

tff(c_1109,plain,
    ( k3_xboole_0('#skF_1',k7_relat_1('#skF_1',k1_relat_1('#skF_2'))) != k7_relat_1('#skF_1',k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1087,c_489])).

tff(c_1169,plain,(
    k3_xboole_0('#skF_1',k7_relat_1('#skF_1',k1_relat_1('#skF_2'))) != k7_relat_1('#skF_1',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_26,c_1109])).

tff(c_1173,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_1169])).

tff(c_1177,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1173])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n023.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 09:48:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.44  
% 2.75/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.45  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.75/1.45  
% 2.75/1.45  %Foreground sorts:
% 2.75/1.45  
% 2.75/1.45  
% 2.75/1.45  %Background operators:
% 2.75/1.45  
% 2.75/1.45  
% 2.75/1.45  %Foreground operators:
% 2.75/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.45  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.75/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.75/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.75/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.75/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.75/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.75/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.75/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.75/1.45  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.75/1.45  
% 3.16/1.46  tff(f_65, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k7_relat_1(A, k1_relat_1(B)) = k7_relat_1(A, k1_relat_1(k7_relat_1(B, k1_relat_1(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t189_relat_1)).
% 3.16/1.46  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.16/1.46  tff(f_39, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.16/1.46  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 3.16/1.46  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.16/1.46  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 3.16/1.46  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.16/1.46  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 3.16/1.46  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_relat_1)).
% 3.16/1.46  tff(c_26, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.16/1.46  tff(c_10, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.16/1.46  tff(c_62, plain, (![A_22, B_23]: (k1_setfam_1(k2_tarski(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.16/1.46  tff(c_96, plain, (![A_29, B_30]: (k1_setfam_1(k2_tarski(A_29, B_30))=k3_xboole_0(B_30, A_29))), inference(superposition, [status(thm), theory('equality')], [c_10, c_62])).
% 3.16/1.46  tff(c_12, plain, (![A_7, B_8]: (k1_setfam_1(k2_tarski(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.16/1.46  tff(c_102, plain, (![B_30, A_29]: (k3_xboole_0(B_30, A_29)=k3_xboole_0(A_29, B_30))), inference(superposition, [status(thm), theory('equality')], [c_96, c_12])).
% 3.16/1.46  tff(c_91, plain, (![B_27, A_28]: (r1_tarski(k7_relat_1(B_27, A_28), B_27) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.16/1.46  tff(c_8, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.16/1.46  tff(c_95, plain, (![B_27, A_28]: (k3_xboole_0(k7_relat_1(B_27, A_28), B_27)=k7_relat_1(B_27, A_28) | ~v1_relat_1(B_27))), inference(resolution, [status(thm)], [c_91, c_8])).
% 3.16/1.46  tff(c_279, plain, (![B_27, A_28]: (k3_xboole_0(B_27, k7_relat_1(B_27, A_28))=k7_relat_1(B_27, A_28) | ~v1_relat_1(B_27))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_95])).
% 3.16/1.46  tff(c_18, plain, (![B_15, A_14]: (k3_xboole_0(k1_relat_1(B_15), A_14)=k1_relat_1(k7_relat_1(B_15, A_14)) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.16/1.46  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.16/1.46  tff(c_163, plain, (![B_35, A_36]: (k7_relat_1(B_35, A_36)=B_35 | ~r1_tarski(k1_relat_1(B_35), A_36) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.16/1.46  tff(c_168, plain, (![B_35]: (k7_relat_1(B_35, k1_relat_1(B_35))=B_35 | ~v1_relat_1(B_35))), inference(resolution, [status(thm)], [c_6, c_163])).
% 3.16/1.46  tff(c_241, plain, (![C_41, A_42, B_43]: (k3_xboole_0(k7_relat_1(C_41, A_42), k7_relat_1(C_41, B_43))=k7_relat_1(C_41, k3_xboole_0(A_42, B_43)) | ~v1_relat_1(C_41))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.16/1.46  tff(c_611, plain, (![B_58, B_59]: (k7_relat_1(B_58, k3_xboole_0(k1_relat_1(B_58), B_59))=k3_xboole_0(B_58, k7_relat_1(B_58, B_59)) | ~v1_relat_1(B_58) | ~v1_relat_1(B_58))), inference(superposition, [status(thm), theory('equality')], [c_168, c_241])).
% 3.16/1.46  tff(c_1087, plain, (![B_72, A_73]: (k7_relat_1(B_72, k1_relat_1(k7_relat_1(B_72, A_73)))=k3_xboole_0(B_72, k7_relat_1(B_72, A_73)) | ~v1_relat_1(B_72) | ~v1_relat_1(B_72) | ~v1_relat_1(B_72))), inference(superposition, [status(thm), theory('equality')], [c_18, c_611])).
% 3.16/1.46  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.16/1.46  tff(c_169, plain, (![B_37, A_38]: (k3_xboole_0(k1_relat_1(B_37), A_38)=k1_relat_1(k7_relat_1(B_37, A_38)) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.16/1.46  tff(c_301, plain, (![A_46, B_47]: (k3_xboole_0(A_46, k1_relat_1(B_47))=k1_relat_1(k7_relat_1(B_47, A_46)) | ~v1_relat_1(B_47))), inference(superposition, [status(thm), theory('equality')], [c_169, c_102])).
% 3.16/1.46  tff(c_393, plain, (![B_54, B_53]: (k1_relat_1(k7_relat_1(B_54, k1_relat_1(B_53)))=k1_relat_1(k7_relat_1(B_53, k1_relat_1(B_54))) | ~v1_relat_1(B_53) | ~v1_relat_1(B_54))), inference(superposition, [status(thm), theory('equality')], [c_18, c_301])).
% 3.16/1.46  tff(c_22, plain, (k7_relat_1('#skF_1', k1_relat_1(k7_relat_1('#skF_2', k1_relat_1('#skF_1'))))!=k7_relat_1('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.16/1.46  tff(c_450, plain, (k7_relat_1('#skF_1', k1_relat_1(k7_relat_1('#skF_1', k1_relat_1('#skF_2'))))!=k7_relat_1('#skF_1', k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_393, c_22])).
% 3.16/1.46  tff(c_489, plain, (k7_relat_1('#skF_1', k1_relat_1(k7_relat_1('#skF_1', k1_relat_1('#skF_2'))))!=k7_relat_1('#skF_1', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_450])).
% 3.16/1.46  tff(c_1109, plain, (k3_xboole_0('#skF_1', k7_relat_1('#skF_1', k1_relat_1('#skF_2')))!=k7_relat_1('#skF_1', k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1087, c_489])).
% 3.16/1.46  tff(c_1169, plain, (k3_xboole_0('#skF_1', k7_relat_1('#skF_1', k1_relat_1('#skF_2')))!=k7_relat_1('#skF_1', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_26, c_1109])).
% 3.16/1.46  tff(c_1173, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_279, c_1169])).
% 3.16/1.46  tff(c_1177, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_1173])).
% 3.16/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.46  
% 3.16/1.46  Inference rules
% 3.16/1.46  ----------------------
% 3.16/1.46  #Ref     : 0
% 3.16/1.46  #Sup     : 319
% 3.16/1.46  #Fact    : 0
% 3.16/1.46  #Define  : 0
% 3.16/1.46  #Split   : 0
% 3.16/1.46  #Chain   : 0
% 3.16/1.46  #Close   : 0
% 3.16/1.46  
% 3.16/1.46  Ordering : KBO
% 3.16/1.46  
% 3.16/1.46  Simplification rules
% 3.16/1.46  ----------------------
% 3.16/1.46  #Subsume      : 58
% 3.16/1.46  #Demod        : 34
% 3.16/1.46  #Tautology    : 87
% 3.16/1.46  #SimpNegUnit  : 0
% 3.16/1.46  #BackRed      : 0
% 3.16/1.46  
% 3.16/1.46  #Partial instantiations: 0
% 3.16/1.46  #Strategies tried      : 1
% 3.16/1.46  
% 3.16/1.46  Timing (in seconds)
% 3.16/1.46  ----------------------
% 3.16/1.46  Preprocessing        : 0.29
% 3.16/1.46  Parsing              : 0.15
% 3.16/1.46  CNF conversion       : 0.02
% 3.16/1.46  Main loop            : 0.41
% 3.16/1.46  Inferencing          : 0.16
% 3.16/1.46  Reduction            : 0.12
% 3.16/1.46  Demodulation         : 0.10
% 3.16/1.46  BG Simplification    : 0.03
% 3.16/1.46  Subsumption          : 0.08
% 3.16/1.46  Abstraction          : 0.03
% 3.16/1.46  MUC search           : 0.00
% 3.16/1.46  Cooper               : 0.00
% 3.16/1.46  Total                : 0.72
% 3.16/1.46  Index Insertion      : 0.00
% 3.16/1.46  Index Deletion       : 0.00
% 3.16/1.46  Index Matching       : 0.00
% 3.16/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
