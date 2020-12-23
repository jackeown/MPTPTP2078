%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:32 EST 2020

% Result     : Theorem 7.64s
% Output     : CNFRefutation 7.64s
% Verified   : 
% Statistics : Number of formulae       :   61 (  91 expanded)
%              Number of leaves         :   26 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :   84 ( 123 expanded)
%              Number of equality atoms :   38 (  63 expanded)
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

tff(f_68,negated_conjecture,(
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

tff(f_41,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,k6_subset_1(k1_relat_1(B),A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [A_11,B_12] : k6_subset_1(A_11,B_12) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [C_19,A_17,B_18] :
      ( k7_relat_1(C_19,k6_subset_1(A_17,B_18)) = k6_subset_1(C_19,k7_relat_1(C_19,B_18))
      | ~ r1_tarski(k1_relat_1(C_19),A_17)
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_551,plain,(
    ! [C_72,A_73,B_74] :
      ( k7_relat_1(C_72,k4_xboole_0(A_73,B_74)) = k4_xboole_0(C_72,k7_relat_1(C_72,B_74))
      | ~ r1_tarski(k1_relat_1(C_72),A_73)
      | ~ v1_relat_1(C_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_22])).

tff(c_568,plain,(
    ! [C_75,B_76] :
      ( k7_relat_1(C_75,k4_xboole_0(k1_relat_1(C_75),B_76)) = k4_xboole_0(C_75,k7_relat_1(C_75,B_76))
      | ~ v1_relat_1(C_75) ) ),
    inference(resolution,[status(thm)],[c_8,c_551])).

tff(c_20,plain,(
    ! [B_16,A_15] :
      ( k1_relat_1(k7_relat_1(B_16,k6_subset_1(k1_relat_1(B_16),A_15))) = k6_subset_1(k1_relat_1(B_16),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_33,plain,(
    ! [B_16,A_15] :
      ( k1_relat_1(k7_relat_1(B_16,k4_xboole_0(k1_relat_1(B_16),A_15))) = k4_xboole_0(k1_relat_1(B_16),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_20])).

tff(c_580,plain,(
    ! [C_75,B_76] :
      ( k1_relat_1(k4_xboole_0(C_75,k7_relat_1(C_75,B_76))) = k4_xboole_0(k1_relat_1(C_75),B_76)
      | ~ v1_relat_1(C_75)
      | ~ v1_relat_1(C_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_568,c_33])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_176,plain,(
    ! [B_45,A_46] :
      ( k3_xboole_0(k1_relat_1(B_45),A_46) = k1_relat_1(k7_relat_1(B_45,A_46))
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_207,plain,(
    ! [B_2,B_45] :
      ( k3_xboole_0(B_2,k1_relat_1(B_45)) = k1_relat_1(k7_relat_1(B_45,B_2))
      | ~ v1_relat_1(B_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_176])).

tff(c_113,plain,(
    ! [A_37,B_38] : k5_xboole_0(A_37,k3_xboole_0(A_37,B_38)) = k4_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_125,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_113])).

tff(c_46,plain,(
    ! [B_29,A_30] : k3_xboole_0(B_29,A_30) = k3_xboole_0(A_30,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_61,plain,(
    ! [B_29,A_30] : r1_tarski(k3_xboole_0(B_29,A_30),A_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_12])).

tff(c_232,plain,(
    ! [B_53,A_54] :
      ( k1_relat_1(k7_relat_1(B_53,A_54)) = A_54
      | ~ r1_tarski(A_54,k1_relat_1(B_53))
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_254,plain,(
    ! [B_53,B_29] :
      ( k1_relat_1(k7_relat_1(B_53,k3_xboole_0(B_29,k1_relat_1(B_53)))) = k3_xboole_0(B_29,k1_relat_1(B_53))
      | ~ v1_relat_1(B_53) ) ),
    inference(resolution,[status(thm)],[c_61,c_232])).

tff(c_346,plain,(
    ! [B_62,B_63] :
      ( k3_xboole_0(B_62,k1_relat_1(B_63)) = k1_relat_1(k7_relat_1(B_63,B_62))
      | ~ v1_relat_1(B_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_176])).

tff(c_128,plain,(
    ! [B_39,A_40] :
      ( B_39 = A_40
      | ~ r1_tarski(B_39,A_40)
      | ~ r1_tarski(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_136,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,k3_xboole_0(A_7,B_8)) ) ),
    inference(resolution,[status(thm)],[c_12,c_128])).

tff(c_931,plain,(
    ! [B_85,B_86] :
      ( k3_xboole_0(B_85,k1_relat_1(B_86)) = B_85
      | ~ r1_tarski(B_85,k1_relat_1(k7_relat_1(B_86,B_85)))
      | ~ v1_relat_1(B_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_136])).

tff(c_934,plain,(
    ! [B_29,B_53] :
      ( k3_xboole_0(k3_xboole_0(B_29,k1_relat_1(B_53)),k1_relat_1(B_53)) = k3_xboole_0(B_29,k1_relat_1(B_53))
      | ~ r1_tarski(k3_xboole_0(B_29,k1_relat_1(B_53)),k3_xboole_0(B_29,k1_relat_1(B_53)))
      | ~ v1_relat_1(B_53)
      | ~ v1_relat_1(B_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_931])).

tff(c_1704,plain,(
    ! [B_100,B_101] :
      ( k3_xboole_0(k1_relat_1(B_100),k3_xboole_0(B_101,k1_relat_1(B_100))) = k3_xboole_0(B_101,k1_relat_1(B_100))
      | ~ v1_relat_1(B_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2,c_934])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1737,plain,(
    ! [B_100,B_101] :
      ( k5_xboole_0(k1_relat_1(B_100),k3_xboole_0(B_101,k1_relat_1(B_100))) = k4_xboole_0(k1_relat_1(B_100),k3_xboole_0(B_101,k1_relat_1(B_100)))
      | ~ v1_relat_1(B_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1704,c_10])).

tff(c_3522,plain,(
    ! [B_127,B_128] :
      ( k4_xboole_0(k1_relat_1(B_127),k3_xboole_0(B_128,k1_relat_1(B_127))) = k4_xboole_0(k1_relat_1(B_127),B_128)
      | ~ v1_relat_1(B_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_1737])).

tff(c_7259,plain,(
    ! [B_168,B_169] :
      ( k4_xboole_0(k1_relat_1(B_168),k1_relat_1(k7_relat_1(B_168,B_169))) = k4_xboole_0(k1_relat_1(B_168),B_169)
      | ~ v1_relat_1(B_168)
      | ~ v1_relat_1(B_168) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_3522])).

tff(c_28,plain,(
    k6_subset_1(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_31,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_28])).

tff(c_7307,plain,
    ( k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_7259,c_31])).

tff(c_7412,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_7307])).

tff(c_7422,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_580,c_7412])).

tff(c_7426,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_7422])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:05:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.64/2.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.64/2.52  
% 7.64/2.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.64/2.52  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 7.64/2.52  
% 7.64/2.52  %Foreground sorts:
% 7.64/2.52  
% 7.64/2.52  
% 7.64/2.52  %Background operators:
% 7.64/2.52  
% 7.64/2.52  
% 7.64/2.52  %Foreground operators:
% 7.64/2.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.64/2.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.64/2.52  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.64/2.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.64/2.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.64/2.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.64/2.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.64/2.52  tff('#skF_2', type, '#skF_2': $i).
% 7.64/2.52  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 7.64/2.52  tff('#skF_1', type, '#skF_1': $i).
% 7.64/2.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.64/2.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.64/2.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.64/2.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.64/2.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.64/2.52  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.64/2.52  
% 7.64/2.54  tff(f_68, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k6_subset_1(k1_relat_1(B), k1_relat_1(k7_relat_1(B, A))) = k1_relat_1(k6_subset_1(B, k7_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t213_relat_1)).
% 7.64/2.54  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.64/2.54  tff(f_41, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 7.64/2.54  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t211_relat_1)).
% 7.64/2.54  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, k6_subset_1(k1_relat_1(B), A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t191_relat_1)).
% 7.64/2.54  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.64/2.54  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 7.64/2.54  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.64/2.54  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 7.64/2.54  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 7.64/2.54  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.64/2.54  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.64/2.54  tff(c_16, plain, (![A_11, B_12]: (k6_subset_1(A_11, B_12)=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.64/2.54  tff(c_22, plain, (![C_19, A_17, B_18]: (k7_relat_1(C_19, k6_subset_1(A_17, B_18))=k6_subset_1(C_19, k7_relat_1(C_19, B_18)) | ~r1_tarski(k1_relat_1(C_19), A_17) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.64/2.54  tff(c_551, plain, (![C_72, A_73, B_74]: (k7_relat_1(C_72, k4_xboole_0(A_73, B_74))=k4_xboole_0(C_72, k7_relat_1(C_72, B_74)) | ~r1_tarski(k1_relat_1(C_72), A_73) | ~v1_relat_1(C_72))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_22])).
% 7.64/2.54  tff(c_568, plain, (![C_75, B_76]: (k7_relat_1(C_75, k4_xboole_0(k1_relat_1(C_75), B_76))=k4_xboole_0(C_75, k7_relat_1(C_75, B_76)) | ~v1_relat_1(C_75))), inference(resolution, [status(thm)], [c_8, c_551])).
% 7.64/2.54  tff(c_20, plain, (![B_16, A_15]: (k1_relat_1(k7_relat_1(B_16, k6_subset_1(k1_relat_1(B_16), A_15)))=k6_subset_1(k1_relat_1(B_16), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.64/2.54  tff(c_33, plain, (![B_16, A_15]: (k1_relat_1(k7_relat_1(B_16, k4_xboole_0(k1_relat_1(B_16), A_15)))=k4_xboole_0(k1_relat_1(B_16), A_15) | ~v1_relat_1(B_16))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_20])).
% 7.64/2.54  tff(c_580, plain, (![C_75, B_76]: (k1_relat_1(k4_xboole_0(C_75, k7_relat_1(C_75, B_76)))=k4_xboole_0(k1_relat_1(C_75), B_76) | ~v1_relat_1(C_75) | ~v1_relat_1(C_75))), inference(superposition, [status(thm), theory('equality')], [c_568, c_33])).
% 7.64/2.54  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.64/2.54  tff(c_176, plain, (![B_45, A_46]: (k3_xboole_0(k1_relat_1(B_45), A_46)=k1_relat_1(k7_relat_1(B_45, A_46)) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.64/2.54  tff(c_207, plain, (![B_2, B_45]: (k3_xboole_0(B_2, k1_relat_1(B_45))=k1_relat_1(k7_relat_1(B_45, B_2)) | ~v1_relat_1(B_45))), inference(superposition, [status(thm), theory('equality')], [c_2, c_176])).
% 7.64/2.54  tff(c_113, plain, (![A_37, B_38]: (k5_xboole_0(A_37, k3_xboole_0(A_37, B_38))=k4_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.64/2.54  tff(c_125, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_113])).
% 7.64/2.54  tff(c_46, plain, (![B_29, A_30]: (k3_xboole_0(B_29, A_30)=k3_xboole_0(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.64/2.54  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.64/2.54  tff(c_61, plain, (![B_29, A_30]: (r1_tarski(k3_xboole_0(B_29, A_30), A_30))), inference(superposition, [status(thm), theory('equality')], [c_46, c_12])).
% 7.64/2.54  tff(c_232, plain, (![B_53, A_54]: (k1_relat_1(k7_relat_1(B_53, A_54))=A_54 | ~r1_tarski(A_54, k1_relat_1(B_53)) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.64/2.54  tff(c_254, plain, (![B_53, B_29]: (k1_relat_1(k7_relat_1(B_53, k3_xboole_0(B_29, k1_relat_1(B_53))))=k3_xboole_0(B_29, k1_relat_1(B_53)) | ~v1_relat_1(B_53))), inference(resolution, [status(thm)], [c_61, c_232])).
% 7.64/2.54  tff(c_346, plain, (![B_62, B_63]: (k3_xboole_0(B_62, k1_relat_1(B_63))=k1_relat_1(k7_relat_1(B_63, B_62)) | ~v1_relat_1(B_63))), inference(superposition, [status(thm), theory('equality')], [c_2, c_176])).
% 7.64/2.54  tff(c_128, plain, (![B_39, A_40]: (B_39=A_40 | ~r1_tarski(B_39, A_40) | ~r1_tarski(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.64/2.54  tff(c_136, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, k3_xboole_0(A_7, B_8)))), inference(resolution, [status(thm)], [c_12, c_128])).
% 7.64/2.54  tff(c_931, plain, (![B_85, B_86]: (k3_xboole_0(B_85, k1_relat_1(B_86))=B_85 | ~r1_tarski(B_85, k1_relat_1(k7_relat_1(B_86, B_85))) | ~v1_relat_1(B_86))), inference(superposition, [status(thm), theory('equality')], [c_346, c_136])).
% 7.64/2.54  tff(c_934, plain, (![B_29, B_53]: (k3_xboole_0(k3_xboole_0(B_29, k1_relat_1(B_53)), k1_relat_1(B_53))=k3_xboole_0(B_29, k1_relat_1(B_53)) | ~r1_tarski(k3_xboole_0(B_29, k1_relat_1(B_53)), k3_xboole_0(B_29, k1_relat_1(B_53))) | ~v1_relat_1(B_53) | ~v1_relat_1(B_53))), inference(superposition, [status(thm), theory('equality')], [c_254, c_931])).
% 7.64/2.54  tff(c_1704, plain, (![B_100, B_101]: (k3_xboole_0(k1_relat_1(B_100), k3_xboole_0(B_101, k1_relat_1(B_100)))=k3_xboole_0(B_101, k1_relat_1(B_100)) | ~v1_relat_1(B_100))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2, c_934])).
% 7.64/2.54  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.64/2.54  tff(c_1737, plain, (![B_100, B_101]: (k5_xboole_0(k1_relat_1(B_100), k3_xboole_0(B_101, k1_relat_1(B_100)))=k4_xboole_0(k1_relat_1(B_100), k3_xboole_0(B_101, k1_relat_1(B_100))) | ~v1_relat_1(B_100))), inference(superposition, [status(thm), theory('equality')], [c_1704, c_10])).
% 7.64/2.54  tff(c_3522, plain, (![B_127, B_128]: (k4_xboole_0(k1_relat_1(B_127), k3_xboole_0(B_128, k1_relat_1(B_127)))=k4_xboole_0(k1_relat_1(B_127), B_128) | ~v1_relat_1(B_127))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_1737])).
% 7.64/2.54  tff(c_7259, plain, (![B_168, B_169]: (k4_xboole_0(k1_relat_1(B_168), k1_relat_1(k7_relat_1(B_168, B_169)))=k4_xboole_0(k1_relat_1(B_168), B_169) | ~v1_relat_1(B_168) | ~v1_relat_1(B_168))), inference(superposition, [status(thm), theory('equality')], [c_207, c_3522])).
% 7.64/2.54  tff(c_28, plain, (k6_subset_1(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.64/2.54  tff(c_31, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_28])).
% 7.64/2.54  tff(c_7307, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_7259, c_31])).
% 7.64/2.54  tff(c_7412, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_7307])).
% 7.64/2.54  tff(c_7422, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_580, c_7412])).
% 7.64/2.54  tff(c_7426, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_7422])).
% 7.64/2.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.64/2.54  
% 7.64/2.54  Inference rules
% 7.64/2.54  ----------------------
% 7.64/2.54  #Ref     : 0
% 7.64/2.54  #Sup     : 2224
% 7.64/2.54  #Fact    : 0
% 7.64/2.54  #Define  : 0
% 7.64/2.54  #Split   : 0
% 7.64/2.54  #Chain   : 0
% 7.64/2.54  #Close   : 0
% 7.64/2.54  
% 7.64/2.54  Ordering : KBO
% 7.64/2.54  
% 7.64/2.54  Simplification rules
% 7.64/2.54  ----------------------
% 7.64/2.54  #Subsume      : 280
% 7.64/2.54  #Demod        : 285
% 7.64/2.54  #Tautology    : 223
% 7.64/2.54  #SimpNegUnit  : 0
% 7.64/2.54  #BackRed      : 0
% 7.64/2.54  
% 7.64/2.54  #Partial instantiations: 0
% 7.64/2.54  #Strategies tried      : 1
% 7.64/2.54  
% 7.64/2.54  Timing (in seconds)
% 7.64/2.54  ----------------------
% 7.64/2.54  Preprocessing        : 0.28
% 7.64/2.54  Parsing              : 0.15
% 7.64/2.54  CNF conversion       : 0.02
% 7.64/2.54  Main loop            : 1.56
% 7.64/2.54  Inferencing          : 0.49
% 7.64/2.54  Reduction            : 0.48
% 7.64/2.54  Demodulation         : 0.37
% 7.64/2.54  BG Simplification    : 0.10
% 7.64/2.54  Subsumption          : 0.40
% 7.64/2.54  Abstraction          : 0.11
% 7.64/2.54  MUC search           : 0.00
% 7.64/2.54  Cooper               : 0.00
% 7.64/2.54  Total                : 1.86
% 7.64/2.54  Index Insertion      : 0.00
% 7.64/2.54  Index Deletion       : 0.00
% 7.64/2.54  Index Matching       : 0.00
% 7.64/2.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
