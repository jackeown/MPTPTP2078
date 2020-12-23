%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:27 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   56 (  67 expanded)
%              Number of leaves         :   27 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   63 (  76 expanded)
%              Number of equality atoms :   34 (  38 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_35,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_37,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k8_relat_1(k2_relat_1(A),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(k3_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_relat_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_112,plain,(
    ! [A_33,B_34] : k1_setfam_1(k2_tarski(A_33,B_34)) = k3_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_127,plain,(
    ! [B_35,A_36] : k1_setfam_1(k2_tarski(B_35,A_36)) = k3_xboole_0(A_36,B_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_112])).

tff(c_10,plain,(
    ! [A_10,B_11] : k1_setfam_1(k2_tarski(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_150,plain,(
    ! [B_37,A_38] : k3_xboole_0(B_37,A_38) = k3_xboole_0(A_38,B_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_10])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_165,plain,(
    ! [B_37,A_38] : r1_tarski(k3_xboole_0(B_37,A_38),A_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_2])).

tff(c_12,plain,(
    ! [A_12] : v1_relat_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ! [A_19] : k2_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_80,plain,(
    ! [A_29] :
      ( k8_relat_1(k2_relat_1(A_29),A_29) = A_29
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_89,plain,(
    ! [A_19] :
      ( k8_relat_1(A_19,k6_relat_1(A_19)) = k6_relat_1(A_19)
      | ~ v1_relat_1(k6_relat_1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_80])).

tff(c_93,plain,(
    ! [A_19] : k8_relat_1(A_19,k6_relat_1(A_19)) = k6_relat_1(A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_89])).

tff(c_20,plain,(
    ! [A_19] : k1_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_223,plain,(
    ! [A_46,B_47] :
      ( k5_relat_1(k6_relat_1(A_46),B_47) = B_47
      | ~ r1_tarski(k1_relat_1(B_47),A_46)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_226,plain,(
    ! [A_46,A_19] :
      ( k5_relat_1(k6_relat_1(A_46),k6_relat_1(A_19)) = k6_relat_1(A_19)
      | ~ r1_tarski(A_19,A_46)
      | ~ v1_relat_1(k6_relat_1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_223])).

tff(c_229,plain,(
    ! [A_48,A_49] :
      ( k5_relat_1(k6_relat_1(A_48),k6_relat_1(A_49)) = k6_relat_1(A_49)
      | ~ r1_tarski(A_49,A_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_226])).

tff(c_14,plain,(
    ! [B_14,A_13] :
      ( k5_relat_1(B_14,k6_relat_1(A_13)) = k8_relat_1(A_13,B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_235,plain,(
    ! [A_49,A_48] :
      ( k8_relat_1(A_49,k6_relat_1(A_48)) = k6_relat_1(A_49)
      | ~ v1_relat_1(k6_relat_1(A_48))
      | ~ r1_tarski(A_49,A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_14])).

tff(c_248,plain,(
    ! [A_49,A_48] :
      ( k8_relat_1(A_49,k6_relat_1(A_48)) = k6_relat_1(A_49)
      | ~ r1_tarski(A_49,A_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_235])).

tff(c_286,plain,(
    ! [A_52,B_53,C_54] :
      ( k8_relat_1(k3_xboole_0(A_52,B_53),C_54) = k8_relat_1(A_52,k8_relat_1(B_53,C_54))
      | ~ v1_relat_1(C_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_304,plain,(
    ! [A_52,B_53,A_48] :
      ( k8_relat_1(A_52,k8_relat_1(B_53,k6_relat_1(A_48))) = k6_relat_1(k3_xboole_0(A_52,B_53))
      | ~ v1_relat_1(k6_relat_1(A_48))
      | ~ r1_tarski(k3_xboole_0(A_52,B_53),A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_286])).

tff(c_823,plain,(
    ! [A_74,B_75,A_76] :
      ( k8_relat_1(A_74,k8_relat_1(B_75,k6_relat_1(A_76))) = k6_relat_1(k3_xboole_0(A_74,B_75))
      | ~ r1_tarski(k3_xboole_0(A_74,B_75),A_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_304])).

tff(c_897,plain,(
    ! [A_74,A_19] :
      ( k8_relat_1(A_74,k6_relat_1(A_19)) = k6_relat_1(k3_xboole_0(A_74,A_19))
      | ~ r1_tarski(k3_xboole_0(A_74,A_19),A_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_823])).

tff(c_918,plain,(
    ! [A_74,A_19] : k8_relat_1(A_74,k6_relat_1(A_19)) = k6_relat_1(k3_xboole_0(A_74,A_19)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_897])).

tff(c_199,plain,(
    ! [B_41,A_42] :
      ( k5_relat_1(B_41,k6_relat_1(A_42)) = k8_relat_1(A_42,B_41)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_205,plain,
    ( k8_relat_1('#skF_1',k6_relat_1('#skF_2')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_26])).

tff(c_211,plain,(
    k8_relat_1('#skF_1',k6_relat_1('#skF_2')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_205])).

tff(c_931,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_918,c_211])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:53:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.40  
% 2.73/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.40  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.73/1.40  
% 2.73/1.40  %Foreground sorts:
% 2.73/1.40  
% 2.73/1.40  
% 2.73/1.40  %Background operators:
% 2.73/1.40  
% 2.73/1.40  
% 2.73/1.40  %Foreground operators:
% 2.73/1.40  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.73/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.40  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.73/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.73/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.73/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.73/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.73/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.73/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.73/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.73/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.73/1.40  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.73/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.73/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.73/1.40  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.73/1.40  
% 2.73/1.41  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.73/1.41  tff(f_35, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.73/1.41  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.73/1.41  tff(f_37, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.73/1.41  tff(f_53, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.73/1.41  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (k8_relat_1(k2_relat_1(A), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_relat_1)).
% 2.73/1.41  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 2.73/1.41  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 2.73/1.41  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(k3_xboole_0(A, B), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_relat_1)).
% 2.73/1.41  tff(f_62, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 2.73/1.41  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.73/1.41  tff(c_112, plain, (![A_33, B_34]: (k1_setfam_1(k2_tarski(A_33, B_34))=k3_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.73/1.41  tff(c_127, plain, (![B_35, A_36]: (k1_setfam_1(k2_tarski(B_35, A_36))=k3_xboole_0(A_36, B_35))), inference(superposition, [status(thm), theory('equality')], [c_4, c_112])).
% 2.73/1.41  tff(c_10, plain, (![A_10, B_11]: (k1_setfam_1(k2_tarski(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.73/1.41  tff(c_150, plain, (![B_37, A_38]: (k3_xboole_0(B_37, A_38)=k3_xboole_0(A_38, B_37))), inference(superposition, [status(thm), theory('equality')], [c_127, c_10])).
% 2.73/1.41  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.73/1.41  tff(c_165, plain, (![B_37, A_38]: (r1_tarski(k3_xboole_0(B_37, A_38), A_38))), inference(superposition, [status(thm), theory('equality')], [c_150, c_2])).
% 2.73/1.41  tff(c_12, plain, (![A_12]: (v1_relat_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.73/1.41  tff(c_22, plain, (![A_19]: (k2_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.73/1.41  tff(c_80, plain, (![A_29]: (k8_relat_1(k2_relat_1(A_29), A_29)=A_29 | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.73/1.41  tff(c_89, plain, (![A_19]: (k8_relat_1(A_19, k6_relat_1(A_19))=k6_relat_1(A_19) | ~v1_relat_1(k6_relat_1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_80])).
% 2.73/1.41  tff(c_93, plain, (![A_19]: (k8_relat_1(A_19, k6_relat_1(A_19))=k6_relat_1(A_19))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_89])).
% 2.73/1.41  tff(c_20, plain, (![A_19]: (k1_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.73/1.41  tff(c_223, plain, (![A_46, B_47]: (k5_relat_1(k6_relat_1(A_46), B_47)=B_47 | ~r1_tarski(k1_relat_1(B_47), A_46) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.73/1.41  tff(c_226, plain, (![A_46, A_19]: (k5_relat_1(k6_relat_1(A_46), k6_relat_1(A_19))=k6_relat_1(A_19) | ~r1_tarski(A_19, A_46) | ~v1_relat_1(k6_relat_1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_223])).
% 2.73/1.41  tff(c_229, plain, (![A_48, A_49]: (k5_relat_1(k6_relat_1(A_48), k6_relat_1(A_49))=k6_relat_1(A_49) | ~r1_tarski(A_49, A_48))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_226])).
% 2.73/1.41  tff(c_14, plain, (![B_14, A_13]: (k5_relat_1(B_14, k6_relat_1(A_13))=k8_relat_1(A_13, B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.73/1.41  tff(c_235, plain, (![A_49, A_48]: (k8_relat_1(A_49, k6_relat_1(A_48))=k6_relat_1(A_49) | ~v1_relat_1(k6_relat_1(A_48)) | ~r1_tarski(A_49, A_48))), inference(superposition, [status(thm), theory('equality')], [c_229, c_14])).
% 2.73/1.41  tff(c_248, plain, (![A_49, A_48]: (k8_relat_1(A_49, k6_relat_1(A_48))=k6_relat_1(A_49) | ~r1_tarski(A_49, A_48))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_235])).
% 2.73/1.41  tff(c_286, plain, (![A_52, B_53, C_54]: (k8_relat_1(k3_xboole_0(A_52, B_53), C_54)=k8_relat_1(A_52, k8_relat_1(B_53, C_54)) | ~v1_relat_1(C_54))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.73/1.41  tff(c_304, plain, (![A_52, B_53, A_48]: (k8_relat_1(A_52, k8_relat_1(B_53, k6_relat_1(A_48)))=k6_relat_1(k3_xboole_0(A_52, B_53)) | ~v1_relat_1(k6_relat_1(A_48)) | ~r1_tarski(k3_xboole_0(A_52, B_53), A_48))), inference(superposition, [status(thm), theory('equality')], [c_248, c_286])).
% 2.73/1.41  tff(c_823, plain, (![A_74, B_75, A_76]: (k8_relat_1(A_74, k8_relat_1(B_75, k6_relat_1(A_76)))=k6_relat_1(k3_xboole_0(A_74, B_75)) | ~r1_tarski(k3_xboole_0(A_74, B_75), A_76))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_304])).
% 2.73/1.41  tff(c_897, plain, (![A_74, A_19]: (k8_relat_1(A_74, k6_relat_1(A_19))=k6_relat_1(k3_xboole_0(A_74, A_19)) | ~r1_tarski(k3_xboole_0(A_74, A_19), A_19))), inference(superposition, [status(thm), theory('equality')], [c_93, c_823])).
% 2.73/1.41  tff(c_918, plain, (![A_74, A_19]: (k8_relat_1(A_74, k6_relat_1(A_19))=k6_relat_1(k3_xboole_0(A_74, A_19)))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_897])).
% 2.73/1.41  tff(c_199, plain, (![B_41, A_42]: (k5_relat_1(B_41, k6_relat_1(A_42))=k8_relat_1(A_42, B_41) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.73/1.41  tff(c_26, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.73/1.41  tff(c_205, plain, (k8_relat_1('#skF_1', k6_relat_1('#skF_2'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_199, c_26])).
% 2.73/1.41  tff(c_211, plain, (k8_relat_1('#skF_1', k6_relat_1('#skF_2'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_205])).
% 2.73/1.41  tff(c_931, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_918, c_211])).
% 2.73/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.41  
% 2.73/1.41  Inference rules
% 2.73/1.41  ----------------------
% 2.73/1.41  #Ref     : 0
% 2.73/1.41  #Sup     : 212
% 2.73/1.41  #Fact    : 0
% 2.73/1.41  #Define  : 0
% 2.73/1.41  #Split   : 1
% 2.73/1.41  #Chain   : 0
% 2.73/1.41  #Close   : 0
% 2.73/1.41  
% 2.73/1.41  Ordering : KBO
% 2.73/1.41  
% 2.73/1.41  Simplification rules
% 2.73/1.41  ----------------------
% 2.73/1.41  #Subsume      : 21
% 2.73/1.41  #Demod        : 86
% 2.73/1.41  #Tautology    : 114
% 2.73/1.41  #SimpNegUnit  : 0
% 2.73/1.41  #BackRed      : 7
% 2.73/1.41  
% 2.73/1.41  #Partial instantiations: 0
% 2.73/1.41  #Strategies tried      : 1
% 2.73/1.41  
% 2.73/1.41  Timing (in seconds)
% 2.73/1.41  ----------------------
% 2.73/1.41  Preprocessing        : 0.30
% 2.73/1.41  Parsing              : 0.16
% 2.73/1.41  CNF conversion       : 0.02
% 2.73/1.41  Main loop            : 0.36
% 2.73/1.41  Inferencing          : 0.13
% 2.73/1.42  Reduction            : 0.14
% 2.73/1.42  Demodulation         : 0.11
% 2.73/1.42  BG Simplification    : 0.02
% 2.73/1.42  Subsumption          : 0.05
% 2.73/1.42  Abstraction          : 0.02
% 2.73/1.42  MUC search           : 0.00
% 2.73/1.42  Cooper               : 0.00
% 2.73/1.42  Total                : 0.69
% 2.73/1.42  Index Insertion      : 0.00
% 2.73/1.42  Index Deletion       : 0.00
% 2.73/1.42  Index Matching       : 0.00
% 2.73/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
