%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:32 EST 2020

% Result     : Theorem 9.62s
% Output     : CNFRefutation 9.62s
% Verified   : 
% Statistics : Number of formulae       :   57 (  88 expanded)
%              Number of leaves         :   25 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :   72 ( 114 expanded)
%              Number of equality atoms :   34 (  62 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k6_subset_1(k1_relat_1(B),k1_relat_1(k7_relat_1(B,A))) = k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t213_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,k6_subset_1(k1_relat_1(B),A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [A_13,B_14] : k6_subset_1(A_13,B_14) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [C_21,A_19,B_20] :
      ( k7_relat_1(C_21,k6_subset_1(A_19,B_20)) = k6_subset_1(C_21,k7_relat_1(C_21,B_20))
      | ~ r1_tarski(k1_relat_1(C_21),A_19)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_484,plain,(
    ! [C_74,A_75,B_76] :
      ( k7_relat_1(C_74,k4_xboole_0(A_75,B_76)) = k4_xboole_0(C_74,k7_relat_1(C_74,B_76))
      | ~ r1_tarski(k1_relat_1(C_74),A_75)
      | ~ v1_relat_1(C_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_24])).

tff(c_1154,plain,(
    ! [C_99,B_100] :
      ( k7_relat_1(C_99,k4_xboole_0(k1_relat_1(C_99),B_100)) = k4_xboole_0(C_99,k7_relat_1(C_99,B_100))
      | ~ v1_relat_1(C_99) ) ),
    inference(resolution,[status(thm)],[c_8,c_484])).

tff(c_22,plain,(
    ! [B_18,A_17] :
      ( k1_relat_1(k7_relat_1(B_18,k6_subset_1(k1_relat_1(B_18),A_17))) = k6_subset_1(k1_relat_1(B_18),A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_35,plain,(
    ! [B_18,A_17] :
      ( k1_relat_1(k7_relat_1(B_18,k4_xboole_0(k1_relat_1(B_18),A_17))) = k4_xboole_0(k1_relat_1(B_18),A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_22])).

tff(c_1166,plain,(
    ! [C_99,B_100] :
      ( k1_relat_1(k4_xboole_0(C_99,k7_relat_1(C_99,B_100))) = k4_xboole_0(k1_relat_1(C_99),B_100)
      | ~ v1_relat_1(C_99)
      | ~ v1_relat_1(C_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1154,c_35])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_192,plain,(
    ! [B_49,A_50] :
      ( k3_xboole_0(k1_relat_1(B_49),A_50) = k1_relat_1(k7_relat_1(B_49,A_50))
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_386,plain,(
    ! [A_70,B_71] :
      ( k3_xboole_0(A_70,k1_relat_1(B_71)) = k1_relat_1(k7_relat_1(B_71,A_70))
      | ~ v1_relat_1(B_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_2])).

tff(c_124,plain,(
    ! [A_41,B_42] : k4_xboole_0(A_41,k4_xboole_0(A_41,B_42)) = k3_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_142,plain,(
    ! [A_43,B_44] : r1_tarski(k3_xboole_0(A_43,B_44),A_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_12])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_151,plain,(
    ! [A_43,B_44] :
      ( k3_xboole_0(A_43,B_44) = A_43
      | ~ r1_tarski(A_43,k3_xboole_0(A_43,B_44)) ) ),
    inference(resolution,[status(thm)],[c_142,c_4])).

tff(c_1378,plain,(
    ! [A_105,B_106] :
      ( k3_xboole_0(A_105,k1_relat_1(B_106)) = A_105
      | ~ r1_tarski(A_105,k1_relat_1(k7_relat_1(B_106,A_105)))
      | ~ v1_relat_1(B_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_386,c_151])).

tff(c_1393,plain,(
    ! [B_18,A_17] :
      ( k3_xboole_0(k4_xboole_0(k1_relat_1(B_18),A_17),k1_relat_1(B_18)) = k4_xboole_0(k1_relat_1(B_18),A_17)
      | ~ r1_tarski(k4_xboole_0(k1_relat_1(B_18),A_17),k4_xboole_0(k1_relat_1(B_18),A_17))
      | ~ v1_relat_1(B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_1378])).

tff(c_1404,plain,(
    ! [B_18,A_17] :
      ( k3_xboole_0(k1_relat_1(B_18),k4_xboole_0(k1_relat_1(B_18),A_17)) = k4_xboole_0(k1_relat_1(B_18),A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2,c_1393])).

tff(c_26,plain,(
    ! [B_23,A_22] :
      ( k3_xboole_0(k1_relat_1(B_23),A_22) = k1_relat_1(k7_relat_1(B_23,A_22))
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_14,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_447,plain,(
    ! [A_72,B_73] : k4_xboole_0(A_72,k3_xboole_0(A_72,B_73)) = k3_xboole_0(A_72,k4_xboole_0(A_72,B_73)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_124])).

tff(c_10608,plain,(
    ! [B_219,A_220] :
      ( k4_xboole_0(k1_relat_1(B_219),k1_relat_1(k7_relat_1(B_219,A_220))) = k3_xboole_0(k1_relat_1(B_219),k4_xboole_0(k1_relat_1(B_219),A_220))
      | ~ v1_relat_1(B_219) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_447])).

tff(c_30,plain,(
    k6_subset_1(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_33,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_30])).

tff(c_10666,plain,
    ( k3_xboole_0(k1_relat_1('#skF_2'),k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10608,c_33])).

tff(c_10771,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_10666])).

tff(c_10785,plain,
    ( k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1404,c_10771])).

tff(c_10790,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_10785])).

tff(c_10795,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1166,c_10790])).

tff(c_10799,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_10795])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n024.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:12:36 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.62/3.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.62/3.38  
% 9.62/3.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.62/3.39  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 9.62/3.39  
% 9.62/3.39  %Foreground sorts:
% 9.62/3.39  
% 9.62/3.39  
% 9.62/3.39  %Background operators:
% 9.62/3.39  
% 9.62/3.39  
% 9.62/3.39  %Foreground operators:
% 9.62/3.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.62/3.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.62/3.39  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.62/3.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.62/3.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.62/3.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.62/3.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.62/3.39  tff('#skF_2', type, '#skF_2': $i).
% 9.62/3.39  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 9.62/3.39  tff('#skF_1', type, '#skF_1': $i).
% 9.62/3.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.62/3.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.62/3.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.62/3.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.62/3.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.62/3.39  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.62/3.39  
% 9.62/3.40  tff(f_70, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k6_subset_1(k1_relat_1(B), k1_relat_1(k7_relat_1(B, A))) = k1_relat_1(k6_subset_1(B, k7_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t213_relat_1)).
% 9.62/3.40  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.62/3.40  tff(f_43, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 9.62/3.40  tff(f_55, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t211_relat_1)).
% 9.62/3.40  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, k6_subset_1(k1_relat_1(B), A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t191_relat_1)).
% 9.62/3.40  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.62/3.40  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 9.62/3.40  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.62/3.40  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 9.62/3.40  tff(c_32, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.62/3.40  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.62/3.40  tff(c_18, plain, (![A_13, B_14]: (k6_subset_1(A_13, B_14)=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.62/3.40  tff(c_24, plain, (![C_21, A_19, B_20]: (k7_relat_1(C_21, k6_subset_1(A_19, B_20))=k6_subset_1(C_21, k7_relat_1(C_21, B_20)) | ~r1_tarski(k1_relat_1(C_21), A_19) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.62/3.40  tff(c_484, plain, (![C_74, A_75, B_76]: (k7_relat_1(C_74, k4_xboole_0(A_75, B_76))=k4_xboole_0(C_74, k7_relat_1(C_74, B_76)) | ~r1_tarski(k1_relat_1(C_74), A_75) | ~v1_relat_1(C_74))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_24])).
% 9.62/3.40  tff(c_1154, plain, (![C_99, B_100]: (k7_relat_1(C_99, k4_xboole_0(k1_relat_1(C_99), B_100))=k4_xboole_0(C_99, k7_relat_1(C_99, B_100)) | ~v1_relat_1(C_99))), inference(resolution, [status(thm)], [c_8, c_484])).
% 9.62/3.40  tff(c_22, plain, (![B_18, A_17]: (k1_relat_1(k7_relat_1(B_18, k6_subset_1(k1_relat_1(B_18), A_17)))=k6_subset_1(k1_relat_1(B_18), A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.62/3.40  tff(c_35, plain, (![B_18, A_17]: (k1_relat_1(k7_relat_1(B_18, k4_xboole_0(k1_relat_1(B_18), A_17)))=k4_xboole_0(k1_relat_1(B_18), A_17) | ~v1_relat_1(B_18))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_22])).
% 9.62/3.40  tff(c_1166, plain, (![C_99, B_100]: (k1_relat_1(k4_xboole_0(C_99, k7_relat_1(C_99, B_100)))=k4_xboole_0(k1_relat_1(C_99), B_100) | ~v1_relat_1(C_99) | ~v1_relat_1(C_99))), inference(superposition, [status(thm), theory('equality')], [c_1154, c_35])).
% 9.62/3.40  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.62/3.40  tff(c_192, plain, (![B_49, A_50]: (k3_xboole_0(k1_relat_1(B_49), A_50)=k1_relat_1(k7_relat_1(B_49, A_50)) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.62/3.40  tff(c_386, plain, (![A_70, B_71]: (k3_xboole_0(A_70, k1_relat_1(B_71))=k1_relat_1(k7_relat_1(B_71, A_70)) | ~v1_relat_1(B_71))), inference(superposition, [status(thm), theory('equality')], [c_192, c_2])).
% 9.62/3.40  tff(c_124, plain, (![A_41, B_42]: (k4_xboole_0(A_41, k4_xboole_0(A_41, B_42))=k3_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.62/3.40  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.62/3.40  tff(c_142, plain, (![A_43, B_44]: (r1_tarski(k3_xboole_0(A_43, B_44), A_43))), inference(superposition, [status(thm), theory('equality')], [c_124, c_12])).
% 9.62/3.40  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.62/3.40  tff(c_151, plain, (![A_43, B_44]: (k3_xboole_0(A_43, B_44)=A_43 | ~r1_tarski(A_43, k3_xboole_0(A_43, B_44)))), inference(resolution, [status(thm)], [c_142, c_4])).
% 9.62/3.40  tff(c_1378, plain, (![A_105, B_106]: (k3_xboole_0(A_105, k1_relat_1(B_106))=A_105 | ~r1_tarski(A_105, k1_relat_1(k7_relat_1(B_106, A_105))) | ~v1_relat_1(B_106))), inference(superposition, [status(thm), theory('equality')], [c_386, c_151])).
% 9.62/3.40  tff(c_1393, plain, (![B_18, A_17]: (k3_xboole_0(k4_xboole_0(k1_relat_1(B_18), A_17), k1_relat_1(B_18))=k4_xboole_0(k1_relat_1(B_18), A_17) | ~r1_tarski(k4_xboole_0(k1_relat_1(B_18), A_17), k4_xboole_0(k1_relat_1(B_18), A_17)) | ~v1_relat_1(B_18) | ~v1_relat_1(B_18))), inference(superposition, [status(thm), theory('equality')], [c_35, c_1378])).
% 9.62/3.40  tff(c_1404, plain, (![B_18, A_17]: (k3_xboole_0(k1_relat_1(B_18), k4_xboole_0(k1_relat_1(B_18), A_17))=k4_xboole_0(k1_relat_1(B_18), A_17) | ~v1_relat_1(B_18))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2, c_1393])).
% 9.62/3.40  tff(c_26, plain, (![B_23, A_22]: (k3_xboole_0(k1_relat_1(B_23), A_22)=k1_relat_1(k7_relat_1(B_23, A_22)) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.62/3.40  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.62/3.40  tff(c_447, plain, (![A_72, B_73]: (k4_xboole_0(A_72, k3_xboole_0(A_72, B_73))=k3_xboole_0(A_72, k4_xboole_0(A_72, B_73)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_124])).
% 9.62/3.40  tff(c_10608, plain, (![B_219, A_220]: (k4_xboole_0(k1_relat_1(B_219), k1_relat_1(k7_relat_1(B_219, A_220)))=k3_xboole_0(k1_relat_1(B_219), k4_xboole_0(k1_relat_1(B_219), A_220)) | ~v1_relat_1(B_219))), inference(superposition, [status(thm), theory('equality')], [c_26, c_447])).
% 9.62/3.40  tff(c_30, plain, (k6_subset_1(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.62/3.40  tff(c_33, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_30])).
% 9.62/3.40  tff(c_10666, plain, (k3_xboole_0(k1_relat_1('#skF_2'), k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10608, c_33])).
% 9.62/3.40  tff(c_10771, plain, (k3_xboole_0(k1_relat_1('#skF_2'), k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_10666])).
% 9.62/3.40  tff(c_10785, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1404, c_10771])).
% 9.62/3.40  tff(c_10790, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_10785])).
% 9.62/3.40  tff(c_10795, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1166, c_10790])).
% 9.62/3.40  tff(c_10799, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_10795])).
% 9.62/3.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.62/3.40  
% 9.62/3.40  Inference rules
% 9.62/3.40  ----------------------
% 9.62/3.40  #Ref     : 0
% 9.62/3.40  #Sup     : 3023
% 9.62/3.40  #Fact    : 0
% 9.62/3.40  #Define  : 0
% 9.62/3.40  #Split   : 0
% 9.62/3.40  #Chain   : 0
% 9.62/3.40  #Close   : 0
% 9.62/3.40  
% 9.62/3.40  Ordering : KBO
% 9.62/3.40  
% 9.62/3.40  Simplification rules
% 9.62/3.40  ----------------------
% 9.62/3.40  #Subsume      : 338
% 9.62/3.40  #Demod        : 1234
% 9.62/3.40  #Tautology    : 420
% 9.62/3.40  #SimpNegUnit  : 0
% 9.62/3.40  #BackRed      : 0
% 9.62/3.40  
% 9.62/3.40  #Partial instantiations: 0
% 9.62/3.40  #Strategies tried      : 1
% 9.62/3.40  
% 9.62/3.40  Timing (in seconds)
% 9.62/3.40  ----------------------
% 9.62/3.40  Preprocessing        : 0.35
% 9.62/3.40  Parsing              : 0.18
% 9.62/3.40  CNF conversion       : 0.02
% 9.62/3.40  Main loop            : 2.24
% 9.62/3.40  Inferencing          : 0.62
% 9.62/3.40  Reduction            : 0.90
% 9.62/3.40  Demodulation         : 0.75
% 9.62/3.40  BG Simplification    : 0.12
% 9.62/3.40  Subsumption          : 0.48
% 9.62/3.40  Abstraction          : 0.16
% 9.62/3.40  MUC search           : 0.00
% 9.62/3.40  Cooper               : 0.00
% 9.62/3.40  Total                : 2.61
% 9.62/3.40  Index Insertion      : 0.00
% 9.62/3.40  Index Deletion       : 0.00
% 9.62/3.40  Index Matching       : 0.00
% 9.62/3.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
