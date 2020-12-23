%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:24 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   55 (  64 expanded)
%              Number of leaves         :   30 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :   54 (  72 expanded)
%              Number of equality atoms :   30 (  39 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_69,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_59,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_35,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_28,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_34,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_382,plain,(
    ! [A_66,C_67,B_68] :
      ( k3_xboole_0(A_66,k10_relat_1(C_67,B_68)) = k10_relat_1(k7_relat_1(C_67,A_66),B_68)
      | ~ v1_relat_1(C_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_12,plain,(
    ! [A_14] : k1_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [A_19] : v1_relat_1(k6_relat_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_187,plain,(
    ! [A_46,B_47] :
      ( k5_relat_1(k6_relat_1(A_46),B_47) = k7_relat_1(B_47,A_46)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_26,plain,(
    ! [B_24,A_23] : k5_relat_1(k6_relat_1(B_24),k6_relat_1(A_23)) = k6_relat_1(k3_xboole_0(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_194,plain,(
    ! [A_23,A_46] :
      ( k7_relat_1(k6_relat_1(A_23),A_46) = k6_relat_1(k3_xboole_0(A_23,A_46))
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_26])).

tff(c_203,plain,(
    ! [A_23,A_46] : k7_relat_1(k6_relat_1(A_23),A_46) = k6_relat_1(k3_xboole_0(A_23,A_46)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_194])).

tff(c_216,plain,(
    ! [B_50,A_51] :
      ( k7_relat_1(B_50,A_51) = B_50
      | ~ r1_tarski(k1_relat_1(B_50),A_51)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_219,plain,(
    ! [A_14,A_51] :
      ( k7_relat_1(k6_relat_1(A_14),A_51) = k6_relat_1(A_14)
      | ~ r1_tarski(A_14,A_51)
      | ~ v1_relat_1(k6_relat_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_216])).

tff(c_223,plain,(
    ! [A_52,A_53] :
      ( k6_relat_1(k3_xboole_0(A_52,A_53)) = k6_relat_1(A_52)
      | ~ r1_tarski(A_52,A_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_203,c_219])).

tff(c_241,plain,(
    ! [A_52,A_53] :
      ( k3_xboole_0(A_52,A_53) = k1_relat_1(k6_relat_1(A_52))
      | ~ r1_tarski(A_52,A_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_12])).

tff(c_267,plain,(
    ! [A_54,A_55] :
      ( k3_xboole_0(A_54,A_55) = A_54
      | ~ r1_tarski(A_54,A_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_241])).

tff(c_271,plain,(
    k3_xboole_0(k10_relat_1('#skF_1','#skF_3'),'#skF_2') = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_267])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_97,plain,(
    ! [A_35,B_36] : k1_setfam_1(k2_tarski(A_35,B_36)) = k3_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_112,plain,(
    ! [B_37,A_38] : k1_setfam_1(k2_tarski(B_37,A_38)) = k3_xboole_0(A_38,B_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_97])).

tff(c_10,plain,(
    ! [A_12,B_13] : k1_setfam_1(k2_tarski(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_118,plain,(
    ! [B_37,A_38] : k3_xboole_0(B_37,A_38) = k3_xboole_0(A_38,B_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_10])).

tff(c_278,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_118])).

tff(c_391,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_278])).

tff(c_417,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_391])).

tff(c_419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_417])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:09:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.31  
% 2.01/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.31  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.01/1.31  
% 2.01/1.31  %Foreground sorts:
% 2.01/1.31  
% 2.01/1.31  
% 2.01/1.31  %Background operators:
% 2.01/1.31  
% 2.01/1.31  
% 2.01/1.31  %Foreground operators:
% 2.01/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.01/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.31  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.01/1.31  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.01/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.01/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.01/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.01/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.01/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.01/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.01/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.01/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.01/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.01/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.31  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.01/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.01/1.31  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.01/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.01/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.01/1.31  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.01/1.31  
% 2.01/1.33  tff(f_69, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 2.01/1.33  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 2.01/1.33  tff(f_39, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.01/1.33  tff(f_53, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.01/1.33  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.01/1.33  tff(f_59, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 2.01/1.33  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 2.01/1.33  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.01/1.33  tff(f_35, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.01/1.33  tff(c_28, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.01/1.33  tff(c_34, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.01/1.33  tff(c_382, plain, (![A_66, C_67, B_68]: (k3_xboole_0(A_66, k10_relat_1(C_67, B_68))=k10_relat_1(k7_relat_1(C_67, A_66), B_68) | ~v1_relat_1(C_67))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.01/1.33  tff(c_30, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.01/1.33  tff(c_12, plain, (![A_14]: (k1_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.01/1.33  tff(c_20, plain, (![A_19]: (v1_relat_1(k6_relat_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.01/1.33  tff(c_187, plain, (![A_46, B_47]: (k5_relat_1(k6_relat_1(A_46), B_47)=k7_relat_1(B_47, A_46) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.01/1.33  tff(c_26, plain, (![B_24, A_23]: (k5_relat_1(k6_relat_1(B_24), k6_relat_1(A_23))=k6_relat_1(k3_xboole_0(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.01/1.33  tff(c_194, plain, (![A_23, A_46]: (k7_relat_1(k6_relat_1(A_23), A_46)=k6_relat_1(k3_xboole_0(A_23, A_46)) | ~v1_relat_1(k6_relat_1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_187, c_26])).
% 2.01/1.33  tff(c_203, plain, (![A_23, A_46]: (k7_relat_1(k6_relat_1(A_23), A_46)=k6_relat_1(k3_xboole_0(A_23, A_46)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_194])).
% 2.01/1.33  tff(c_216, plain, (![B_50, A_51]: (k7_relat_1(B_50, A_51)=B_50 | ~r1_tarski(k1_relat_1(B_50), A_51) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.01/1.33  tff(c_219, plain, (![A_14, A_51]: (k7_relat_1(k6_relat_1(A_14), A_51)=k6_relat_1(A_14) | ~r1_tarski(A_14, A_51) | ~v1_relat_1(k6_relat_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_216])).
% 2.01/1.33  tff(c_223, plain, (![A_52, A_53]: (k6_relat_1(k3_xboole_0(A_52, A_53))=k6_relat_1(A_52) | ~r1_tarski(A_52, A_53))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_203, c_219])).
% 2.01/1.33  tff(c_241, plain, (![A_52, A_53]: (k3_xboole_0(A_52, A_53)=k1_relat_1(k6_relat_1(A_52)) | ~r1_tarski(A_52, A_53))), inference(superposition, [status(thm), theory('equality')], [c_223, c_12])).
% 2.01/1.33  tff(c_267, plain, (![A_54, A_55]: (k3_xboole_0(A_54, A_55)=A_54 | ~r1_tarski(A_54, A_55))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_241])).
% 2.01/1.33  tff(c_271, plain, (k3_xboole_0(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_267])).
% 2.01/1.33  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.01/1.33  tff(c_97, plain, (![A_35, B_36]: (k1_setfam_1(k2_tarski(A_35, B_36))=k3_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.01/1.33  tff(c_112, plain, (![B_37, A_38]: (k1_setfam_1(k2_tarski(B_37, A_38))=k3_xboole_0(A_38, B_37))), inference(superposition, [status(thm), theory('equality')], [c_2, c_97])).
% 2.01/1.33  tff(c_10, plain, (![A_12, B_13]: (k1_setfam_1(k2_tarski(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.01/1.33  tff(c_118, plain, (![B_37, A_38]: (k3_xboole_0(B_37, A_38)=k3_xboole_0(A_38, B_37))), inference(superposition, [status(thm), theory('equality')], [c_112, c_10])).
% 2.01/1.33  tff(c_278, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_271, c_118])).
% 2.01/1.33  tff(c_391, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_382, c_278])).
% 2.01/1.33  tff(c_417, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_391])).
% 2.01/1.33  tff(c_419, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_417])).
% 2.01/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.33  
% 2.01/1.33  Inference rules
% 2.01/1.33  ----------------------
% 2.01/1.33  #Ref     : 0
% 2.01/1.33  #Sup     : 96
% 2.01/1.33  #Fact    : 0
% 2.01/1.33  #Define  : 0
% 2.01/1.33  #Split   : 0
% 2.01/1.33  #Chain   : 0
% 2.01/1.33  #Close   : 0
% 2.01/1.33  
% 2.01/1.33  Ordering : KBO
% 2.01/1.33  
% 2.01/1.33  Simplification rules
% 2.01/1.33  ----------------------
% 2.01/1.33  #Subsume      : 6
% 2.01/1.33  #Demod        : 29
% 2.01/1.33  #Tautology    : 59
% 2.01/1.33  #SimpNegUnit  : 1
% 2.01/1.33  #BackRed      : 0
% 2.01/1.33  
% 2.01/1.33  #Partial instantiations: 0
% 2.01/1.33  #Strategies tried      : 1
% 2.01/1.33  
% 2.01/1.33  Timing (in seconds)
% 2.01/1.33  ----------------------
% 2.01/1.33  Preprocessing        : 0.30
% 2.01/1.33  Parsing              : 0.17
% 2.01/1.33  CNF conversion       : 0.02
% 2.01/1.33  Main loop            : 0.20
% 2.01/1.33  Inferencing          : 0.08
% 2.01/1.33  Reduction            : 0.08
% 2.01/1.33  Demodulation         : 0.06
% 2.01/1.33  BG Simplification    : 0.01
% 2.01/1.33  Subsumption          : 0.03
% 2.01/1.33  Abstraction          : 0.02
% 2.01/1.33  MUC search           : 0.00
% 2.01/1.33  Cooper               : 0.00
% 2.31/1.33  Total                : 0.53
% 2.31/1.33  Index Insertion      : 0.00
% 2.31/1.33  Index Deletion       : 0.00
% 2.31/1.33  Index Matching       : 0.00
% 2.31/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
