%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:32 EST 2020

% Result     : Theorem 10.44s
% Output     : CNFRefutation 10.52s
% Verified   : 
% Statistics : Number of formulae       :   53 (  69 expanded)
%              Number of leaves         :   25 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   62 (  83 expanded)
%              Number of equality atoms :   30 (  45 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k6_subset_1(k1_relat_1(B),k1_relat_1(k7_relat_1(B,A))) = k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t213_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [A_13,B_14] : k6_subset_1(A_13,B_14) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [C_19,A_17,B_18] :
      ( k7_relat_1(C_19,k6_subset_1(A_17,B_18)) = k6_subset_1(C_19,k7_relat_1(C_19,B_18))
      | ~ r1_tarski(k1_relat_1(C_19),A_17)
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_653,plain,(
    ! [C_59,A_60,B_61] :
      ( k7_relat_1(C_59,k4_xboole_0(A_60,B_61)) = k4_xboole_0(C_59,k7_relat_1(C_59,B_61))
      | ~ r1_tarski(k1_relat_1(C_59),A_60)
      | ~ v1_relat_1(C_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_22])).

tff(c_657,plain,(
    ! [C_59,B_61] :
      ( k7_relat_1(C_59,k4_xboole_0(k1_relat_1(C_59),B_61)) = k4_xboole_0(C_59,k7_relat_1(C_59,B_61))
      | ~ v1_relat_1(C_59) ) ),
    inference(resolution,[status(thm)],[c_8,c_653])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_179,plain,(
    ! [B_43,A_44] :
      ( k3_xboole_0(k1_relat_1(B_43),A_44) = k1_relat_1(k7_relat_1(B_43,A_44))
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1565,plain,(
    ! [B_84,B_85] :
      ( k3_xboole_0(B_84,k1_relat_1(B_85)) = k1_relat_1(k7_relat_1(B_85,B_84))
      | ~ v1_relat_1(B_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_179])).

tff(c_16,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_102,plain,(
    ! [A_35,B_36] :
      ( k3_xboole_0(A_35,B_36) = A_35
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_116,plain,(
    ! [A_11,B_12] : k3_xboole_0(k4_xboole_0(A_11,B_12),A_11) = k4_xboole_0(A_11,B_12) ),
    inference(resolution,[status(thm)],[c_16,c_102])).

tff(c_6687,plain,(
    ! [B_160,B_161] :
      ( k1_relat_1(k7_relat_1(B_160,k4_xboole_0(k1_relat_1(B_160),B_161))) = k4_xboole_0(k1_relat_1(B_160),B_161)
      | ~ v1_relat_1(B_160) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1565,c_116])).

tff(c_12774,plain,(
    ! [C_218,B_219] :
      ( k1_relat_1(k4_xboole_0(C_218,k7_relat_1(C_218,B_219))) = k4_xboole_0(k1_relat_1(C_218),B_219)
      | ~ v1_relat_1(C_218)
      | ~ v1_relat_1(C_218) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_657,c_6687])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_24,plain,(
    ! [B_21,A_20] :
      ( k3_xboole_0(k1_relat_1(B_21),A_20) = k1_relat_1(k7_relat_1(B_21,A_20))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_254,plain,(
    ! [A_47,B_48] : k3_xboole_0(k3_xboole_0(A_47,B_48),A_47) = k3_xboole_0(A_47,B_48) ),
    inference(resolution,[status(thm)],[c_12,c_102])).

tff(c_287,plain,(
    ! [B_21,A_20] :
      ( k3_xboole_0(k1_relat_1(k7_relat_1(B_21,A_20)),k1_relat_1(B_21)) = k3_xboole_0(k1_relat_1(B_21),A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_254])).

tff(c_4155,plain,(
    ! [B_132,A_133] :
      ( k3_xboole_0(k1_relat_1(B_132),k1_relat_1(k7_relat_1(B_132,A_133))) = k3_xboole_0(k1_relat_1(B_132),A_133)
      | ~ v1_relat_1(B_132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_287])).

tff(c_4276,plain,(
    ! [B_132,A_133] :
      ( k5_xboole_0(k1_relat_1(B_132),k3_xboole_0(k1_relat_1(B_132),A_133)) = k4_xboole_0(k1_relat_1(B_132),k1_relat_1(k7_relat_1(B_132,A_133)))
      | ~ v1_relat_1(B_132) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4155,c_10])).

tff(c_10290,plain,(
    ! [B_197,A_198] :
      ( k4_xboole_0(k1_relat_1(B_197),k1_relat_1(k7_relat_1(B_197,A_198))) = k4_xboole_0(k1_relat_1(B_197),A_198)
      | ~ v1_relat_1(B_197) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_4276])).

tff(c_26,plain,(
    k6_subset_1(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_30,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_26])).

tff(c_10333,plain,
    ( k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10290,c_30])).

tff(c_10386,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_10333])).

tff(c_12804,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12774,c_10386])).

tff(c_12901,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_12804])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:42:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.44/3.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.44/3.43  
% 10.44/3.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.52/3.43  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 10.52/3.43  
% 10.52/3.43  %Foreground sorts:
% 10.52/3.43  
% 10.52/3.43  
% 10.52/3.43  %Background operators:
% 10.52/3.43  
% 10.52/3.43  
% 10.52/3.43  %Foreground operators:
% 10.52/3.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.52/3.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.52/3.43  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 10.52/3.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.52/3.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.52/3.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.52/3.43  tff('#skF_2', type, '#skF_2': $i).
% 10.52/3.43  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 10.52/3.43  tff('#skF_1', type, '#skF_1': $i).
% 10.52/3.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.52/3.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.52/3.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.52/3.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.52/3.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.52/3.43  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.52/3.43  
% 10.52/3.44  tff(f_62, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k6_subset_1(k1_relat_1(B), k1_relat_1(k7_relat_1(B, A))) = k1_relat_1(k6_subset_1(B, k7_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t213_relat_1)).
% 10.52/3.44  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.52/3.44  tff(f_45, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 10.52/3.44  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t211_relat_1)).
% 10.52/3.44  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.52/3.44  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 10.52/3.44  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 10.52/3.44  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 10.52/3.44  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.52/3.44  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 10.52/3.44  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.52/3.44  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.52/3.44  tff(c_18, plain, (![A_13, B_14]: (k6_subset_1(A_13, B_14)=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.52/3.44  tff(c_22, plain, (![C_19, A_17, B_18]: (k7_relat_1(C_19, k6_subset_1(A_17, B_18))=k6_subset_1(C_19, k7_relat_1(C_19, B_18)) | ~r1_tarski(k1_relat_1(C_19), A_17) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.52/3.44  tff(c_653, plain, (![C_59, A_60, B_61]: (k7_relat_1(C_59, k4_xboole_0(A_60, B_61))=k4_xboole_0(C_59, k7_relat_1(C_59, B_61)) | ~r1_tarski(k1_relat_1(C_59), A_60) | ~v1_relat_1(C_59))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_22])).
% 10.52/3.44  tff(c_657, plain, (![C_59, B_61]: (k7_relat_1(C_59, k4_xboole_0(k1_relat_1(C_59), B_61))=k4_xboole_0(C_59, k7_relat_1(C_59, B_61)) | ~v1_relat_1(C_59))), inference(resolution, [status(thm)], [c_8, c_653])).
% 10.52/3.44  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.52/3.44  tff(c_179, plain, (![B_43, A_44]: (k3_xboole_0(k1_relat_1(B_43), A_44)=k1_relat_1(k7_relat_1(B_43, A_44)) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.52/3.44  tff(c_1565, plain, (![B_84, B_85]: (k3_xboole_0(B_84, k1_relat_1(B_85))=k1_relat_1(k7_relat_1(B_85, B_84)) | ~v1_relat_1(B_85))), inference(superposition, [status(thm), theory('equality')], [c_2, c_179])).
% 10.52/3.44  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.52/3.44  tff(c_102, plain, (![A_35, B_36]: (k3_xboole_0(A_35, B_36)=A_35 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.52/3.44  tff(c_116, plain, (![A_11, B_12]: (k3_xboole_0(k4_xboole_0(A_11, B_12), A_11)=k4_xboole_0(A_11, B_12))), inference(resolution, [status(thm)], [c_16, c_102])).
% 10.52/3.44  tff(c_6687, plain, (![B_160, B_161]: (k1_relat_1(k7_relat_1(B_160, k4_xboole_0(k1_relat_1(B_160), B_161)))=k4_xboole_0(k1_relat_1(B_160), B_161) | ~v1_relat_1(B_160))), inference(superposition, [status(thm), theory('equality')], [c_1565, c_116])).
% 10.52/3.44  tff(c_12774, plain, (![C_218, B_219]: (k1_relat_1(k4_xboole_0(C_218, k7_relat_1(C_218, B_219)))=k4_xboole_0(k1_relat_1(C_218), B_219) | ~v1_relat_1(C_218) | ~v1_relat_1(C_218))), inference(superposition, [status(thm), theory('equality')], [c_657, c_6687])).
% 10.52/3.45  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.52/3.45  tff(c_24, plain, (![B_21, A_20]: (k3_xboole_0(k1_relat_1(B_21), A_20)=k1_relat_1(k7_relat_1(B_21, A_20)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.52/3.45  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.52/3.45  tff(c_254, plain, (![A_47, B_48]: (k3_xboole_0(k3_xboole_0(A_47, B_48), A_47)=k3_xboole_0(A_47, B_48))), inference(resolution, [status(thm)], [c_12, c_102])).
% 10.52/3.45  tff(c_287, plain, (![B_21, A_20]: (k3_xboole_0(k1_relat_1(k7_relat_1(B_21, A_20)), k1_relat_1(B_21))=k3_xboole_0(k1_relat_1(B_21), A_20) | ~v1_relat_1(B_21))), inference(superposition, [status(thm), theory('equality')], [c_24, c_254])).
% 10.52/3.45  tff(c_4155, plain, (![B_132, A_133]: (k3_xboole_0(k1_relat_1(B_132), k1_relat_1(k7_relat_1(B_132, A_133)))=k3_xboole_0(k1_relat_1(B_132), A_133) | ~v1_relat_1(B_132))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_287])).
% 10.52/3.45  tff(c_4276, plain, (![B_132, A_133]: (k5_xboole_0(k1_relat_1(B_132), k3_xboole_0(k1_relat_1(B_132), A_133))=k4_xboole_0(k1_relat_1(B_132), k1_relat_1(k7_relat_1(B_132, A_133))) | ~v1_relat_1(B_132))), inference(superposition, [status(thm), theory('equality')], [c_4155, c_10])).
% 10.52/3.45  tff(c_10290, plain, (![B_197, A_198]: (k4_xboole_0(k1_relat_1(B_197), k1_relat_1(k7_relat_1(B_197, A_198)))=k4_xboole_0(k1_relat_1(B_197), A_198) | ~v1_relat_1(B_197))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_4276])).
% 10.52/3.45  tff(c_26, plain, (k6_subset_1(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.52/3.45  tff(c_30, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_26])).
% 10.52/3.45  tff(c_10333, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10290, c_30])).
% 10.52/3.45  tff(c_10386, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_10333])).
% 10.52/3.45  tff(c_12804, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12774, c_10386])).
% 10.52/3.45  tff(c_12901, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_12804])).
% 10.52/3.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.52/3.45  
% 10.52/3.45  Inference rules
% 10.52/3.45  ----------------------
% 10.52/3.45  #Ref     : 0
% 10.52/3.45  #Sup     : 3330
% 10.52/3.45  #Fact    : 0
% 10.52/3.45  #Define  : 0
% 10.52/3.45  #Split   : 0
% 10.52/3.45  #Chain   : 0
% 10.52/3.45  #Close   : 0
% 10.52/3.45  
% 10.52/3.45  Ordering : KBO
% 10.52/3.45  
% 10.52/3.45  Simplification rules
% 10.52/3.45  ----------------------
% 10.52/3.45  #Subsume      : 607
% 10.52/3.45  #Demod        : 4724
% 10.52/3.45  #Tautology    : 1447
% 10.52/3.45  #SimpNegUnit  : 0
% 10.52/3.45  #BackRed      : 2
% 10.52/3.45  
% 10.52/3.45  #Partial instantiations: 0
% 10.52/3.45  #Strategies tried      : 1
% 10.52/3.45  
% 10.52/3.45  Timing (in seconds)
% 10.52/3.45  ----------------------
% 10.52/3.45  Preprocessing        : 0.30
% 10.52/3.45  Parsing              : 0.16
% 10.52/3.45  CNF conversion       : 0.02
% 10.52/3.45  Main loop            : 2.39
% 10.52/3.45  Inferencing          : 0.54
% 10.52/3.45  Reduction            : 1.31
% 10.52/3.45  Demodulation         : 1.16
% 10.52/3.45  BG Simplification    : 0.07
% 10.52/3.45  Subsumption          : 0.37
% 10.52/3.45  Abstraction          : 0.14
% 10.52/3.45  MUC search           : 0.00
% 10.52/3.45  Cooper               : 0.00
% 10.52/3.45  Total                : 2.72
% 10.52/3.45  Index Insertion      : 0.00
% 10.52/3.45  Index Deletion       : 0.00
% 10.52/3.45  Index Matching       : 0.00
% 10.52/3.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
