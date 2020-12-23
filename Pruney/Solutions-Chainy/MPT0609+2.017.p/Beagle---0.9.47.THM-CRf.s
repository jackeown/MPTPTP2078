%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:33 EST 2020

% Result     : Theorem 12.60s
% Output     : CNFRefutation 12.60s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 109 expanded)
%              Number of leaves         :   23 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :   68 ( 128 expanded)
%              Number of equality atoms :   39 (  83 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_60,negated_conjecture,(
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

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [A_13,B_14] : k6_subset_1(A_13,B_14) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ! [C_17,A_15,B_16] :
      ( k7_relat_1(C_17,k6_subset_1(A_15,B_16)) = k6_subset_1(C_17,k7_relat_1(C_17,B_16))
      | ~ r1_tarski(k1_relat_1(C_17),A_15)
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_637,plain,(
    ! [C_55,A_56,B_57] :
      ( k7_relat_1(C_55,k4_xboole_0(A_56,B_57)) = k4_xboole_0(C_55,k7_relat_1(C_55,B_57))
      | ~ r1_tarski(k1_relat_1(C_55),A_56)
      | ~ v1_relat_1(C_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_20])).

tff(c_644,plain,(
    ! [C_55,B_57] :
      ( k7_relat_1(C_55,k4_xboole_0(k1_relat_1(C_55),B_57)) = k4_xboole_0(C_55,k7_relat_1(C_55,B_57))
      | ~ v1_relat_1(C_55) ) ),
    inference(resolution,[status(thm)],[c_8,c_637])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_80,plain,(
    ! [A_27,B_28] :
      ( k3_xboole_0(A_27,B_28) = A_27
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_249,plain,(
    ! [A_43,B_44] : k3_xboole_0(k3_xboole_0(A_43,B_44),A_43) = k3_xboole_0(A_43,B_44) ),
    inference(resolution,[status(thm)],[c_12,c_80])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_148,plain,(
    ! [A_36,B_37] : k5_xboole_0(A_36,k3_xboole_0(A_36,B_37)) = k4_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_163,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_148])).

tff(c_258,plain,(
    ! [A_43,B_44] : k5_xboole_0(A_43,k3_xboole_0(A_43,B_44)) = k4_xboole_0(A_43,k3_xboole_0(A_43,B_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_163])).

tff(c_302,plain,(
    ! [A_43,B_44] : k4_xboole_0(A_43,k3_xboole_0(A_43,B_44)) = k4_xboole_0(A_43,B_44) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_258])).

tff(c_16,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_133,plain,(
    ! [A_34,B_35] : k4_xboole_0(A_34,k4_xboole_0(A_34,B_35)) = k3_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_142,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,k4_xboole_0(A_11,B_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_133])).

tff(c_1495,plain,(
    ! [A_11,B_12] : k3_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_142])).

tff(c_87,plain,(
    ! [A_7,B_8] : k3_xboole_0(k3_xboole_0(A_7,B_8),A_7) = k3_xboole_0(A_7,B_8) ),
    inference(resolution,[status(thm)],[c_12,c_80])).

tff(c_206,plain,(
    ! [B_41,A_42] :
      ( k3_xboole_0(k1_relat_1(B_41),A_42) = k1_relat_1(k7_relat_1(B_41,A_42))
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1205,plain,(
    ! [A_72,B_73] :
      ( k3_xboole_0(A_72,k1_relat_1(B_73)) = k1_relat_1(k7_relat_1(B_73,A_72))
      | ~ v1_relat_1(B_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_2])).

tff(c_5735,plain,(
    ! [B_146,B_147] :
      ( k1_relat_1(k7_relat_1(B_146,k3_xboole_0(k1_relat_1(B_146),B_147))) = k3_xboole_0(k1_relat_1(B_146),B_147)
      | ~ v1_relat_1(B_146) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_1205])).

tff(c_5838,plain,(
    ! [B_146,B_12] :
      ( k3_xboole_0(k1_relat_1(B_146),k4_xboole_0(k1_relat_1(B_146),B_12)) = k1_relat_1(k7_relat_1(B_146,k4_xboole_0(k1_relat_1(B_146),B_12)))
      | ~ v1_relat_1(B_146) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1495,c_5735])).

tff(c_12631,plain,(
    ! [B_219,B_220] :
      ( k1_relat_1(k7_relat_1(B_219,k4_xboole_0(k1_relat_1(B_219),B_220))) = k4_xboole_0(k1_relat_1(B_219),B_220)
      | ~ v1_relat_1(B_219) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1495,c_5838])).

tff(c_21486,plain,(
    ! [C_297,B_298] :
      ( k1_relat_1(k4_xboole_0(C_297,k7_relat_1(C_297,B_298))) = k4_xboole_0(k1_relat_1(C_297),B_298)
      | ~ v1_relat_1(C_297)
      | ~ v1_relat_1(C_297) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_644,c_12631])).

tff(c_22,plain,(
    ! [B_19,A_18] :
      ( k3_xboole_0(k1_relat_1(B_19),A_18) = k1_relat_1(k7_relat_1(B_19,A_18))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_647,plain,(
    ! [A_58,B_59] : k4_xboole_0(A_58,k3_xboole_0(A_58,B_59)) = k4_xboole_0(A_58,B_59) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_258])).

tff(c_11135,plain,(
    ! [B_208,A_209] :
      ( k4_xboole_0(k1_relat_1(B_208),k1_relat_1(k7_relat_1(B_208,A_209))) = k4_xboole_0(k1_relat_1(B_208),A_209)
      | ~ v1_relat_1(B_208) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_647])).

tff(c_24,plain,(
    k6_subset_1(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_27,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_24])).

tff(c_11187,plain,
    ( k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_11135,c_27])).

tff(c_11245,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_11187])).

tff(c_21591,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_21486,c_11245])).

tff(c_21713,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_21591])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:02:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.60/4.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.60/4.81  
% 12.60/4.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.60/4.81  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1
% 12.60/4.81  
% 12.60/4.81  %Foreground sorts:
% 12.60/4.81  
% 12.60/4.81  
% 12.60/4.81  %Background operators:
% 12.60/4.81  
% 12.60/4.81  
% 12.60/4.81  %Foreground operators:
% 12.60/4.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.60/4.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.60/4.81  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 12.60/4.81  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.60/4.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.60/4.81  tff('#skF_2', type, '#skF_2': $i).
% 12.60/4.81  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 12.60/4.81  tff('#skF_1', type, '#skF_1': $i).
% 12.60/4.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.60/4.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.60/4.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.60/4.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.60/4.81  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.60/4.81  
% 12.60/4.82  tff(f_60, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k6_subset_1(k1_relat_1(B), k1_relat_1(k7_relat_1(B, A))) = k1_relat_1(k6_subset_1(B, k7_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t213_relat_1)).
% 12.60/4.82  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.60/4.82  tff(f_45, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 12.60/4.82  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t211_relat_1)).
% 12.60/4.82  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 12.60/4.82  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 12.60/4.82  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 12.60/4.82  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 12.60/4.82  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 12.60/4.82  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 12.60/4.82  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.60/4.82  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.60/4.82  tff(c_18, plain, (![A_13, B_14]: (k6_subset_1(A_13, B_14)=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.60/4.82  tff(c_20, plain, (![C_17, A_15, B_16]: (k7_relat_1(C_17, k6_subset_1(A_15, B_16))=k6_subset_1(C_17, k7_relat_1(C_17, B_16)) | ~r1_tarski(k1_relat_1(C_17), A_15) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.60/4.82  tff(c_637, plain, (![C_55, A_56, B_57]: (k7_relat_1(C_55, k4_xboole_0(A_56, B_57))=k4_xboole_0(C_55, k7_relat_1(C_55, B_57)) | ~r1_tarski(k1_relat_1(C_55), A_56) | ~v1_relat_1(C_55))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_20])).
% 12.60/4.82  tff(c_644, plain, (![C_55, B_57]: (k7_relat_1(C_55, k4_xboole_0(k1_relat_1(C_55), B_57))=k4_xboole_0(C_55, k7_relat_1(C_55, B_57)) | ~v1_relat_1(C_55))), inference(resolution, [status(thm)], [c_8, c_637])).
% 12.60/4.82  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.60/4.82  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.60/4.82  tff(c_80, plain, (![A_27, B_28]: (k3_xboole_0(A_27, B_28)=A_27 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.60/4.82  tff(c_249, plain, (![A_43, B_44]: (k3_xboole_0(k3_xboole_0(A_43, B_44), A_43)=k3_xboole_0(A_43, B_44))), inference(resolution, [status(thm)], [c_12, c_80])).
% 12.60/4.82  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.60/4.82  tff(c_148, plain, (![A_36, B_37]: (k5_xboole_0(A_36, k3_xboole_0(A_36, B_37))=k4_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.60/4.82  tff(c_163, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_148])).
% 12.60/4.82  tff(c_258, plain, (![A_43, B_44]: (k5_xboole_0(A_43, k3_xboole_0(A_43, B_44))=k4_xboole_0(A_43, k3_xboole_0(A_43, B_44)))), inference(superposition, [status(thm), theory('equality')], [c_249, c_163])).
% 12.60/4.82  tff(c_302, plain, (![A_43, B_44]: (k4_xboole_0(A_43, k3_xboole_0(A_43, B_44))=k4_xboole_0(A_43, B_44))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_258])).
% 12.60/4.82  tff(c_16, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.60/4.82  tff(c_133, plain, (![A_34, B_35]: (k4_xboole_0(A_34, k4_xboole_0(A_34, B_35))=k3_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.60/4.82  tff(c_142, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k3_xboole_0(A_11, k4_xboole_0(A_11, B_12)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_133])).
% 12.60/4.82  tff(c_1495, plain, (![A_11, B_12]: (k3_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_302, c_142])).
% 12.60/4.82  tff(c_87, plain, (![A_7, B_8]: (k3_xboole_0(k3_xboole_0(A_7, B_8), A_7)=k3_xboole_0(A_7, B_8))), inference(resolution, [status(thm)], [c_12, c_80])).
% 12.60/4.82  tff(c_206, plain, (![B_41, A_42]: (k3_xboole_0(k1_relat_1(B_41), A_42)=k1_relat_1(k7_relat_1(B_41, A_42)) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_55])).
% 12.60/4.82  tff(c_1205, plain, (![A_72, B_73]: (k3_xboole_0(A_72, k1_relat_1(B_73))=k1_relat_1(k7_relat_1(B_73, A_72)) | ~v1_relat_1(B_73))), inference(superposition, [status(thm), theory('equality')], [c_206, c_2])).
% 12.60/4.82  tff(c_5735, plain, (![B_146, B_147]: (k1_relat_1(k7_relat_1(B_146, k3_xboole_0(k1_relat_1(B_146), B_147)))=k3_xboole_0(k1_relat_1(B_146), B_147) | ~v1_relat_1(B_146))), inference(superposition, [status(thm), theory('equality')], [c_87, c_1205])).
% 12.60/4.82  tff(c_5838, plain, (![B_146, B_12]: (k3_xboole_0(k1_relat_1(B_146), k4_xboole_0(k1_relat_1(B_146), B_12))=k1_relat_1(k7_relat_1(B_146, k4_xboole_0(k1_relat_1(B_146), B_12))) | ~v1_relat_1(B_146))), inference(superposition, [status(thm), theory('equality')], [c_1495, c_5735])).
% 12.60/4.82  tff(c_12631, plain, (![B_219, B_220]: (k1_relat_1(k7_relat_1(B_219, k4_xboole_0(k1_relat_1(B_219), B_220)))=k4_xboole_0(k1_relat_1(B_219), B_220) | ~v1_relat_1(B_219))), inference(demodulation, [status(thm), theory('equality')], [c_1495, c_5838])).
% 12.60/4.82  tff(c_21486, plain, (![C_297, B_298]: (k1_relat_1(k4_xboole_0(C_297, k7_relat_1(C_297, B_298)))=k4_xboole_0(k1_relat_1(C_297), B_298) | ~v1_relat_1(C_297) | ~v1_relat_1(C_297))), inference(superposition, [status(thm), theory('equality')], [c_644, c_12631])).
% 12.60/4.82  tff(c_22, plain, (![B_19, A_18]: (k3_xboole_0(k1_relat_1(B_19), A_18)=k1_relat_1(k7_relat_1(B_19, A_18)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 12.60/4.82  tff(c_647, plain, (![A_58, B_59]: (k4_xboole_0(A_58, k3_xboole_0(A_58, B_59))=k4_xboole_0(A_58, B_59))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_258])).
% 12.60/4.82  tff(c_11135, plain, (![B_208, A_209]: (k4_xboole_0(k1_relat_1(B_208), k1_relat_1(k7_relat_1(B_208, A_209)))=k4_xboole_0(k1_relat_1(B_208), A_209) | ~v1_relat_1(B_208))), inference(superposition, [status(thm), theory('equality')], [c_22, c_647])).
% 12.60/4.82  tff(c_24, plain, (k6_subset_1(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.60/4.82  tff(c_27, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_24])).
% 12.60/4.82  tff(c_11187, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_11135, c_27])).
% 12.60/4.82  tff(c_11245, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_11187])).
% 12.60/4.82  tff(c_21591, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_21486, c_11245])).
% 12.60/4.82  tff(c_21713, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_21591])).
% 12.60/4.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.60/4.82  
% 12.60/4.82  Inference rules
% 12.60/4.82  ----------------------
% 12.60/4.82  #Ref     : 0
% 12.60/4.82  #Sup     : 5650
% 12.60/4.82  #Fact    : 0
% 12.60/4.82  #Define  : 0
% 12.60/4.82  #Split   : 0
% 12.60/4.82  #Chain   : 0
% 12.60/4.82  #Close   : 0
% 12.60/4.82  
% 12.60/4.82  Ordering : KBO
% 12.60/4.82  
% 12.60/4.82  Simplification rules
% 12.60/4.82  ----------------------
% 12.60/4.82  #Subsume      : 929
% 12.60/4.82  #Demod        : 8220
% 12.60/4.82  #Tautology    : 2293
% 12.60/4.82  #SimpNegUnit  : 0
% 12.60/4.82  #BackRed      : 2
% 12.60/4.82  
% 12.60/4.82  #Partial instantiations: 0
% 12.60/4.82  #Strategies tried      : 1
% 12.60/4.82  
% 12.60/4.82  Timing (in seconds)
% 12.60/4.82  ----------------------
% 12.60/4.83  Preprocessing        : 0.28
% 12.60/4.83  Parsing              : 0.15
% 12.60/4.83  CNF conversion       : 0.02
% 12.60/4.83  Main loop            : 3.78
% 12.60/4.83  Inferencing          : 0.73
% 12.60/4.83  Reduction            : 2.07
% 12.60/4.83  Demodulation         : 1.84
% 12.60/4.83  BG Simplification    : 0.10
% 12.60/4.83  Subsumption          : 0.71
% 12.60/4.83  Abstraction          : 0.21
% 12.60/4.83  MUC search           : 0.00
% 12.60/4.83  Cooper               : 0.00
% 12.60/4.83  Total                : 4.10
% 12.60/4.83  Index Insertion      : 0.00
% 12.60/4.83  Index Deletion       : 0.00
% 12.60/4.83  Index Matching       : 0.00
% 12.60/4.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
