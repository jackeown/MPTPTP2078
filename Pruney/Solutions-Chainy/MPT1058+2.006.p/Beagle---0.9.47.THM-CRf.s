%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:22 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   54 (  63 expanded)
%              Number of leaves         :   28 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :   56 (  74 expanded)
%              Number of equality atoms :   31 (  40 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_43,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_51,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_75,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_36,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_42,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_10,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_108,plain,(
    ! [A_40,B_41] : k1_setfam_1(k2_tarski(A_40,B_41)) = k3_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_123,plain,(
    ! [B_42,A_43] : k1_setfam_1(k2_tarski(B_42,A_43)) = k3_xboole_0(A_43,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_108])).

tff(c_14,plain,(
    ! [A_10,B_11] : k1_setfam_1(k2_tarski(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_129,plain,(
    ! [B_42,A_43] : k3_xboole_0(B_42,A_43) = k3_xboole_0(A_43,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_14])).

tff(c_38,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_18,plain,(
    ! [A_14] : k1_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,(
    ! [A_21] : v1_relat_1(k6_relat_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_226,plain,(
    ! [B_56,A_57] : k5_relat_1(k6_relat_1(B_56),k6_relat_1(A_57)) = k6_relat_1(k3_xboole_0(A_57,B_56)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_24,plain,(
    ! [A_17,B_18] :
      ( k5_relat_1(k6_relat_1(A_17),B_18) = k7_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_232,plain,(
    ! [A_57,B_56] :
      ( k7_relat_1(k6_relat_1(A_57),B_56) = k6_relat_1(k3_xboole_0(A_57,B_56))
      | ~ v1_relat_1(k6_relat_1(A_57)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_24])).

tff(c_242,plain,(
    ! [A_57,B_56] : k7_relat_1(k6_relat_1(A_57),B_56) = k6_relat_1(k3_xboole_0(A_57,B_56)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_232])).

tff(c_246,plain,(
    ! [B_58,A_59] :
      ( k7_relat_1(B_58,A_59) = B_58
      | ~ r1_tarski(k1_relat_1(B_58),A_59)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_252,plain,(
    ! [A_14,A_59] :
      ( k7_relat_1(k6_relat_1(A_14),A_59) = k6_relat_1(A_14)
      | ~ r1_tarski(A_14,A_59)
      | ~ v1_relat_1(k6_relat_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_246])).

tff(c_259,plain,(
    ! [A_14,A_59] :
      ( k7_relat_1(k6_relat_1(A_14),A_59) = k6_relat_1(A_14)
      | ~ r1_tarski(A_14,A_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_252])).

tff(c_805,plain,(
    ! [A_91,A_92] :
      ( k6_relat_1(k3_xboole_0(A_91,A_92)) = k6_relat_1(A_91)
      | ~ r1_tarski(A_91,A_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_259])).

tff(c_826,plain,(
    ! [A_91,A_92] :
      ( k3_xboole_0(A_91,A_92) = k1_relat_1(k6_relat_1(A_91))
      | ~ r1_tarski(A_91,A_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_805,c_18])).

tff(c_862,plain,(
    ! [A_93,A_94] :
      ( k3_xboole_0(A_93,A_94) = A_93
      | ~ r1_tarski(A_93,A_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_826])).

tff(c_911,plain,(
    k3_xboole_0(k10_relat_1('#skF_1','#skF_3'),'#skF_2') = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_862])).

tff(c_951,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_911])).

tff(c_32,plain,(
    ! [A_22,C_24,B_23] :
      ( k3_xboole_0(A_22,k10_relat_1(C_24,B_23)) = k10_relat_1(k7_relat_1(C_24,A_22),B_23)
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1625,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_951,c_32])).

tff(c_1647,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1625])).

tff(c_1649,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1647])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:41:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.21/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.49  
% 3.21/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.50  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.21/1.50  
% 3.21/1.50  %Foreground sorts:
% 3.21/1.50  
% 3.21/1.50  
% 3.21/1.50  %Background operators:
% 3.21/1.50  
% 3.21/1.50  
% 3.21/1.50  %Foreground operators:
% 3.21/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.21/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.21/1.50  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.21/1.50  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.21/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.21/1.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.21/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.21/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.21/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.21/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.21/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.21/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.21/1.50  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.21/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.21/1.50  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.21/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.21/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.21/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.21/1.50  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.21/1.50  
% 3.36/1.51  tff(f_85, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 3.36/1.51  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.36/1.51  tff(f_43, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.36/1.51  tff(f_51, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.36/1.51  tff(f_69, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.36/1.51  tff(f_75, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 3.36/1.51  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 3.36/1.51  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 3.36/1.51  tff(f_73, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 3.36/1.51  tff(c_36, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.36/1.51  tff(c_42, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.36/1.51  tff(c_10, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.36/1.51  tff(c_108, plain, (![A_40, B_41]: (k1_setfam_1(k2_tarski(A_40, B_41))=k3_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.36/1.51  tff(c_123, plain, (![B_42, A_43]: (k1_setfam_1(k2_tarski(B_42, A_43))=k3_xboole_0(A_43, B_42))), inference(superposition, [status(thm), theory('equality')], [c_10, c_108])).
% 3.36/1.51  tff(c_14, plain, (![A_10, B_11]: (k1_setfam_1(k2_tarski(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.36/1.51  tff(c_129, plain, (![B_42, A_43]: (k3_xboole_0(B_42, A_43)=k3_xboole_0(A_43, B_42))), inference(superposition, [status(thm), theory('equality')], [c_123, c_14])).
% 3.36/1.51  tff(c_38, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.36/1.51  tff(c_18, plain, (![A_14]: (k1_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.36/1.51  tff(c_28, plain, (![A_21]: (v1_relat_1(k6_relat_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.36/1.51  tff(c_226, plain, (![B_56, A_57]: (k5_relat_1(k6_relat_1(B_56), k6_relat_1(A_57))=k6_relat_1(k3_xboole_0(A_57, B_56)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.36/1.51  tff(c_24, plain, (![A_17, B_18]: (k5_relat_1(k6_relat_1(A_17), B_18)=k7_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.36/1.51  tff(c_232, plain, (![A_57, B_56]: (k7_relat_1(k6_relat_1(A_57), B_56)=k6_relat_1(k3_xboole_0(A_57, B_56)) | ~v1_relat_1(k6_relat_1(A_57)))), inference(superposition, [status(thm), theory('equality')], [c_226, c_24])).
% 3.36/1.51  tff(c_242, plain, (![A_57, B_56]: (k7_relat_1(k6_relat_1(A_57), B_56)=k6_relat_1(k3_xboole_0(A_57, B_56)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_232])).
% 3.36/1.51  tff(c_246, plain, (![B_58, A_59]: (k7_relat_1(B_58, A_59)=B_58 | ~r1_tarski(k1_relat_1(B_58), A_59) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.36/1.51  tff(c_252, plain, (![A_14, A_59]: (k7_relat_1(k6_relat_1(A_14), A_59)=k6_relat_1(A_14) | ~r1_tarski(A_14, A_59) | ~v1_relat_1(k6_relat_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_246])).
% 3.36/1.51  tff(c_259, plain, (![A_14, A_59]: (k7_relat_1(k6_relat_1(A_14), A_59)=k6_relat_1(A_14) | ~r1_tarski(A_14, A_59))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_252])).
% 3.36/1.51  tff(c_805, plain, (![A_91, A_92]: (k6_relat_1(k3_xboole_0(A_91, A_92))=k6_relat_1(A_91) | ~r1_tarski(A_91, A_92))), inference(demodulation, [status(thm), theory('equality')], [c_242, c_259])).
% 3.36/1.51  tff(c_826, plain, (![A_91, A_92]: (k3_xboole_0(A_91, A_92)=k1_relat_1(k6_relat_1(A_91)) | ~r1_tarski(A_91, A_92))), inference(superposition, [status(thm), theory('equality')], [c_805, c_18])).
% 3.36/1.51  tff(c_862, plain, (![A_93, A_94]: (k3_xboole_0(A_93, A_94)=A_93 | ~r1_tarski(A_93, A_94))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_826])).
% 3.36/1.51  tff(c_911, plain, (k3_xboole_0(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_862])).
% 3.36/1.51  tff(c_951, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_129, c_911])).
% 3.36/1.51  tff(c_32, plain, (![A_22, C_24, B_23]: (k3_xboole_0(A_22, k10_relat_1(C_24, B_23))=k10_relat_1(k7_relat_1(C_24, A_22), B_23) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.36/1.51  tff(c_1625, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_951, c_32])).
% 3.36/1.51  tff(c_1647, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1625])).
% 3.36/1.51  tff(c_1649, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_1647])).
% 3.36/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.51  
% 3.36/1.51  Inference rules
% 3.36/1.51  ----------------------
% 3.36/1.51  #Ref     : 0
% 3.36/1.51  #Sup     : 386
% 3.36/1.51  #Fact    : 0
% 3.36/1.51  #Define  : 0
% 3.36/1.51  #Split   : 1
% 3.36/1.51  #Chain   : 0
% 3.36/1.51  #Close   : 0
% 3.36/1.51  
% 3.36/1.51  Ordering : KBO
% 3.36/1.51  
% 3.36/1.51  Simplification rules
% 3.36/1.51  ----------------------
% 3.36/1.51  #Subsume      : 15
% 3.36/1.51  #Demod        : 226
% 3.36/1.51  #Tautology    : 206
% 3.36/1.51  #SimpNegUnit  : 1
% 3.36/1.51  #BackRed      : 0
% 3.36/1.51  
% 3.36/1.51  #Partial instantiations: 0
% 3.36/1.51  #Strategies tried      : 1
% 3.36/1.51  
% 3.36/1.51  Timing (in seconds)
% 3.36/1.51  ----------------------
% 3.36/1.51  Preprocessing        : 0.31
% 3.36/1.51  Parsing              : 0.16
% 3.36/1.51  CNF conversion       : 0.02
% 3.36/1.51  Main loop            : 0.45
% 3.36/1.51  Inferencing          : 0.14
% 3.36/1.51  Reduction            : 0.18
% 3.36/1.51  Demodulation         : 0.14
% 3.36/1.51  BG Simplification    : 0.02
% 3.36/1.51  Subsumption          : 0.07
% 3.36/1.51  Abstraction          : 0.03
% 3.36/1.51  MUC search           : 0.00
% 3.36/1.51  Cooper               : 0.00
% 3.36/1.51  Total                : 0.78
% 3.36/1.51  Index Insertion      : 0.00
% 3.36/1.51  Index Deletion       : 0.00
% 3.36/1.51  Index Matching       : 0.00
% 3.36/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
