%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:22 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :   50 (  59 expanded)
%              Number of leaves         :   26 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :   52 (  70 expanded)
%              Number of equality atoms :   28 (  37 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_43,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_51,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_34,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_40,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_10,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_106,plain,(
    ! [A_38,B_39] : k1_setfam_1(k2_tarski(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_121,plain,(
    ! [B_40,A_41] : k1_setfam_1(k2_tarski(B_40,A_41)) = k3_xboole_0(A_41,B_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_106])).

tff(c_14,plain,(
    ! [A_10,B_11] : k1_setfam_1(k2_tarski(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_127,plain,(
    ! [B_40,A_41] : k3_xboole_0(B_40,A_41) = k3_xboole_0(A_41,B_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_14])).

tff(c_36,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_18,plain,(
    ! [A_14] : k1_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,(
    ! [A_21] : v1_relat_1(k6_relat_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_215,plain,(
    ! [B_52,A_53] :
      ( k7_relat_1(B_52,A_53) = B_52
      | ~ r1_tarski(k1_relat_1(B_52),A_53)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_221,plain,(
    ! [A_14,A_53] :
      ( k7_relat_1(k6_relat_1(A_14),A_53) = k6_relat_1(A_14)
      | ~ r1_tarski(A_14,A_53)
      | ~ v1_relat_1(k6_relat_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_215])).

tff(c_733,plain,(
    ! [A_84,A_85] :
      ( k7_relat_1(k6_relat_1(A_84),A_85) = k6_relat_1(A_84)
      | ~ r1_tarski(A_84,A_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_221])).

tff(c_251,plain,(
    ! [B_55,A_56] :
      ( k3_xboole_0(k1_relat_1(B_55),A_56) = k1_relat_1(k7_relat_1(B_55,A_56))
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_274,plain,(
    ! [A_14,A_56] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_14),A_56)) = k3_xboole_0(A_14,A_56)
      | ~ v1_relat_1(k6_relat_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_251])).

tff(c_278,plain,(
    ! [A_14,A_56] : k1_relat_1(k7_relat_1(k6_relat_1(A_14),A_56)) = k3_xboole_0(A_14,A_56) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_274])).

tff(c_743,plain,(
    ! [A_84,A_85] :
      ( k3_xboole_0(A_84,A_85) = k1_relat_1(k6_relat_1(A_84))
      | ~ r1_tarski(A_84,A_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_733,c_278])).

tff(c_789,plain,(
    ! [A_86,A_87] :
      ( k3_xboole_0(A_86,A_87) = A_86
      | ~ r1_tarski(A_86,A_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_743])).

tff(c_838,plain,(
    k3_xboole_0(k10_relat_1('#skF_1','#skF_3'),'#skF_2') = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_789])).

tff(c_936,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_838])).

tff(c_32,plain,(
    ! [A_22,C_24,B_23] :
      ( k3_xboole_0(A_22,k10_relat_1(C_24,B_23)) = k10_relat_1(k7_relat_1(C_24,A_22),B_23)
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1142,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_936,c_32])).

tff(c_1162,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1142])).

tff(c_1164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1162])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:33:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.44  
% 3.10/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.44  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.10/1.44  
% 3.10/1.44  %Foreground sorts:
% 3.10/1.44  
% 3.10/1.44  
% 3.10/1.44  %Background operators:
% 3.10/1.44  
% 3.10/1.44  
% 3.10/1.44  %Foreground operators:
% 3.10/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.10/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.10/1.44  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.10/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.10/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.10/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.10/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.10/1.44  tff('#skF_2', type, '#skF_2': $i).
% 3.10/1.44  tff('#skF_3', type, '#skF_3': $i).
% 3.10/1.44  tff('#skF_1', type, '#skF_1': $i).
% 3.10/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.10/1.44  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.10/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.10/1.44  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.10/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.10/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.10/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.10/1.44  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.10/1.44  
% 3.10/1.45  tff(f_83, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 3.10/1.45  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.10/1.45  tff(f_43, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.10/1.45  tff(f_51, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.10/1.45  tff(f_69, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.10/1.45  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 3.10/1.45  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 3.10/1.45  tff(f_73, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 3.10/1.45  tff(c_34, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.10/1.45  tff(c_40, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.10/1.45  tff(c_10, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.10/1.45  tff(c_106, plain, (![A_38, B_39]: (k1_setfam_1(k2_tarski(A_38, B_39))=k3_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.10/1.45  tff(c_121, plain, (![B_40, A_41]: (k1_setfam_1(k2_tarski(B_40, A_41))=k3_xboole_0(A_41, B_40))), inference(superposition, [status(thm), theory('equality')], [c_10, c_106])).
% 3.10/1.45  tff(c_14, plain, (![A_10, B_11]: (k1_setfam_1(k2_tarski(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.10/1.45  tff(c_127, plain, (![B_40, A_41]: (k3_xboole_0(B_40, A_41)=k3_xboole_0(A_41, B_40))), inference(superposition, [status(thm), theory('equality')], [c_121, c_14])).
% 3.10/1.45  tff(c_36, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.10/1.45  tff(c_18, plain, (![A_14]: (k1_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.10/1.45  tff(c_28, plain, (![A_21]: (v1_relat_1(k6_relat_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.10/1.45  tff(c_215, plain, (![B_52, A_53]: (k7_relat_1(B_52, A_53)=B_52 | ~r1_tarski(k1_relat_1(B_52), A_53) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.10/1.45  tff(c_221, plain, (![A_14, A_53]: (k7_relat_1(k6_relat_1(A_14), A_53)=k6_relat_1(A_14) | ~r1_tarski(A_14, A_53) | ~v1_relat_1(k6_relat_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_215])).
% 3.10/1.45  tff(c_733, plain, (![A_84, A_85]: (k7_relat_1(k6_relat_1(A_84), A_85)=k6_relat_1(A_84) | ~r1_tarski(A_84, A_85))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_221])).
% 3.10/1.45  tff(c_251, plain, (![B_55, A_56]: (k3_xboole_0(k1_relat_1(B_55), A_56)=k1_relat_1(k7_relat_1(B_55, A_56)) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.10/1.45  tff(c_274, plain, (![A_14, A_56]: (k1_relat_1(k7_relat_1(k6_relat_1(A_14), A_56))=k3_xboole_0(A_14, A_56) | ~v1_relat_1(k6_relat_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_251])).
% 3.10/1.45  tff(c_278, plain, (![A_14, A_56]: (k1_relat_1(k7_relat_1(k6_relat_1(A_14), A_56))=k3_xboole_0(A_14, A_56))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_274])).
% 3.10/1.45  tff(c_743, plain, (![A_84, A_85]: (k3_xboole_0(A_84, A_85)=k1_relat_1(k6_relat_1(A_84)) | ~r1_tarski(A_84, A_85))), inference(superposition, [status(thm), theory('equality')], [c_733, c_278])).
% 3.10/1.45  tff(c_789, plain, (![A_86, A_87]: (k3_xboole_0(A_86, A_87)=A_86 | ~r1_tarski(A_86, A_87))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_743])).
% 3.10/1.45  tff(c_838, plain, (k3_xboole_0(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_789])).
% 3.10/1.45  tff(c_936, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_127, c_838])).
% 3.10/1.45  tff(c_32, plain, (![A_22, C_24, B_23]: (k3_xboole_0(A_22, k10_relat_1(C_24, B_23))=k10_relat_1(k7_relat_1(C_24, A_22), B_23) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.10/1.45  tff(c_1142, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_936, c_32])).
% 3.10/1.45  tff(c_1162, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1142])).
% 3.10/1.45  tff(c_1164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_1162])).
% 3.10/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.45  
% 3.10/1.45  Inference rules
% 3.10/1.45  ----------------------
% 3.10/1.45  #Ref     : 0
% 3.10/1.45  #Sup     : 269
% 3.10/1.45  #Fact    : 0
% 3.10/1.45  #Define  : 0
% 3.10/1.45  #Split   : 1
% 3.10/1.45  #Chain   : 0
% 3.10/1.45  #Close   : 0
% 3.10/1.45  
% 3.10/1.45  Ordering : KBO
% 3.10/1.45  
% 3.10/1.45  Simplification rules
% 3.10/1.45  ----------------------
% 3.10/1.45  #Subsume      : 9
% 3.10/1.45  #Demod        : 121
% 3.10/1.45  #Tautology    : 132
% 3.10/1.45  #SimpNegUnit  : 1
% 3.10/1.45  #BackRed      : 0
% 3.10/1.46  
% 3.10/1.46  #Partial instantiations: 0
% 3.10/1.46  #Strategies tried      : 1
% 3.10/1.46  
% 3.10/1.46  Timing (in seconds)
% 3.10/1.46  ----------------------
% 3.10/1.46  Preprocessing        : 0.31
% 3.10/1.46  Parsing              : 0.16
% 3.10/1.46  CNF conversion       : 0.02
% 3.10/1.46  Main loop            : 0.38
% 3.10/1.46  Inferencing          : 0.13
% 3.10/1.46  Reduction            : 0.14
% 3.10/1.46  Demodulation         : 0.11
% 3.10/1.46  BG Simplification    : 0.02
% 3.10/1.46  Subsumption          : 0.07
% 3.10/1.46  Abstraction          : 0.02
% 3.10/1.46  MUC search           : 0.00
% 3.10/1.46  Cooper               : 0.00
% 3.10/1.46  Total                : 0.72
% 3.10/1.46  Index Insertion      : 0.00
% 3.10/1.46  Index Deletion       : 0.00
% 3.10/1.46  Index Matching       : 0.00
% 3.10/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
