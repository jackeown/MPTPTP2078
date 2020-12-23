%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:13 EST 2020

% Result     : Theorem 6.05s
% Output     : CNFRefutation 6.05s
% Verified   : 
% Statistics : Number of formulae       :   72 (  98 expanded)
%              Number of leaves         :   26 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   70 ( 112 expanded)
%              Number of equality atoms :   48 (  65 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_55,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_57,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_2428,plain,(
    ! [A_121,B_122] :
      ( r1_xboole_0(A_121,B_122)
      | k3_xboole_0(A_121,B_122) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_201,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | k4_xboole_0(A_46,B_47) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_34,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_131,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_209,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_201,c_131])).

tff(c_168,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k2_xboole_0(A_39,B_40)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [A_18,B_19] : r1_tarski(k4_xboole_0(A_18,B_19),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_173,plain,(
    ! [A_39] : r1_tarski(k1_xboole_0,A_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_22])).

tff(c_188,plain,(
    ! [A_44,B_45] :
      ( k3_xboole_0(A_44,B_45) = A_44
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_210,plain,(
    ! [A_48] : k3_xboole_0(k1_xboole_0,A_48) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_173,c_188])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_219,plain,(
    ! [A_48] : k3_xboole_0(A_48,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_2])).

tff(c_281,plain,(
    ! [A_50,B_51] :
      ( k4_xboole_0(A_50,B_51) = k1_xboole_0
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_296,plain,(
    ! [A_18,B_19] : k4_xboole_0(k4_xboole_0(A_18,B_19),A_18) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_281])).

tff(c_36,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_200,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_36,c_188])).

tff(c_970,plain,(
    ! [A_80,B_81,C_82] : k4_xboole_0(k3_xboole_0(A_80,B_81),C_82) = k3_xboole_0(A_80,k4_xboole_0(B_81,C_82)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2228,plain,(
    ! [C_109] : k3_xboole_0('#skF_1',k4_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_109)) = k4_xboole_0('#skF_1',C_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_970])).

tff(c_2270,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_2228])).

tff(c_2280,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_2270])).

tff(c_2282,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_209,c_2280])).

tff(c_2283,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_2432,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2428,c_2283])).

tff(c_24,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k2_xboole_0(A_20,B_21)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_18,plain,(
    ! [A_14,B_15] : k3_xboole_0(A_14,k2_xboole_0(A_14,B_15)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2539,plain,(
    ! [A_132,B_133] : k5_xboole_0(A_132,k3_xboole_0(A_132,B_133)) = k4_xboole_0(A_132,B_133) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2564,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k2_xboole_0(A_14,B_15)) = k5_xboole_0(A_14,A_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2539])).

tff(c_2582,plain,(
    ! [A_14] : k5_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2564])).

tff(c_2284,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_2341,plain,(
    ! [A_117,B_118] :
      ( k3_xboole_0(A_117,B_118) = A_117
      | ~ r1_tarski(A_117,B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2355,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2284,c_2341])).

tff(c_3238,plain,(
    ! [A_155,B_156,C_157] : k4_xboole_0(k3_xboole_0(A_155,B_156),C_157) = k3_xboole_0(A_155,k4_xboole_0(B_156,C_157)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5141,plain,(
    ! [C_189] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_189)) = k4_xboole_0('#skF_1',C_189) ),
    inference(superposition,[status(thm),theory(equality)],[c_2355,c_3238])).

tff(c_2357,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_36,c_2341])).

tff(c_5165,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_5141,c_2357])).

tff(c_14,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_47,plain,(
    ! [B_34,A_35] : k5_xboole_0(B_34,A_35) = k5_xboole_0(A_35,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28,plain,(
    ! [A_25] : k5_xboole_0(A_25,k1_xboole_0) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_63,plain,(
    ! [A_35] : k5_xboole_0(k1_xboole_0,A_35) = A_35 ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_28])).

tff(c_2998,plain,(
    ! [A_148,B_149,C_150] : k5_xboole_0(k5_xboole_0(A_148,B_149),C_150) = k5_xboole_0(A_148,k5_xboole_0(B_149,C_150)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3042,plain,(
    ! [A_14,C_150] : k5_xboole_0(A_14,k5_xboole_0(A_14,C_150)) = k5_xboole_0(k1_xboole_0,C_150) ),
    inference(superposition,[status(thm),theory(equality)],[c_2582,c_2998])).

tff(c_3087,plain,(
    ! [A_151,C_152] : k5_xboole_0(A_151,k5_xboole_0(A_151,C_152)) = C_152 ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_3042])).

tff(c_8011,plain,(
    ! [A_219,B_220] : k5_xboole_0(A_219,k4_xboole_0(A_219,B_220)) = k3_xboole_0(A_219,B_220) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_3087])).

tff(c_8071,plain,(
    k5_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5165,c_8011])).

tff(c_8125,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2582,c_8071])).

tff(c_8127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2432,c_8125])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:31:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.05/2.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.05/2.30  
% 6.05/2.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.05/2.30  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.05/2.30  
% 6.05/2.30  %Foreground sorts:
% 6.05/2.30  
% 6.05/2.30  
% 6.05/2.30  %Background operators:
% 6.05/2.30  
% 6.05/2.30  
% 6.05/2.30  %Foreground operators:
% 6.05/2.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.05/2.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.05/2.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.05/2.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.05/2.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.05/2.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.05/2.30  tff('#skF_2', type, '#skF_2': $i).
% 6.05/2.30  tff('#skF_3', type, '#skF_3': $i).
% 6.05/2.30  tff('#skF_1', type, '#skF_1': $i).
% 6.05/2.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.05/2.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.05/2.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.05/2.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.05/2.30  
% 6.05/2.31  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 6.05/2.31  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.05/2.31  tff(f_66, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 6.05/2.31  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 6.05/2.31  tff(f_49, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.05/2.31  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.05/2.31  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.05/2.31  tff(f_53, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 6.05/2.31  tff(f_43, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 6.05/2.31  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.05/2.31  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 6.05/2.31  tff(f_55, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 6.05/2.31  tff(f_57, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.05/2.31  tff(c_2428, plain, (![A_121, B_122]: (r1_xboole_0(A_121, B_122) | k3_xboole_0(A_121, B_122)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.05/2.31  tff(c_201, plain, (![A_46, B_47]: (r1_tarski(A_46, B_47) | k4_xboole_0(A_46, B_47)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.05/2.31  tff(c_34, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.05/2.31  tff(c_131, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_34])).
% 6.05/2.31  tff(c_209, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_201, c_131])).
% 6.05/2.31  tff(c_168, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k2_xboole_0(A_39, B_40))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.05/2.31  tff(c_22, plain, (![A_18, B_19]: (r1_tarski(k4_xboole_0(A_18, B_19), A_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.05/2.31  tff(c_173, plain, (![A_39]: (r1_tarski(k1_xboole_0, A_39))), inference(superposition, [status(thm), theory('equality')], [c_168, c_22])).
% 6.05/2.31  tff(c_188, plain, (![A_44, B_45]: (k3_xboole_0(A_44, B_45)=A_44 | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.05/2.31  tff(c_210, plain, (![A_48]: (k3_xboole_0(k1_xboole_0, A_48)=k1_xboole_0)), inference(resolution, [status(thm)], [c_173, c_188])).
% 6.05/2.31  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.05/2.31  tff(c_219, plain, (![A_48]: (k3_xboole_0(A_48, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_210, c_2])).
% 6.05/2.31  tff(c_281, plain, (![A_50, B_51]: (k4_xboole_0(A_50, B_51)=k1_xboole_0 | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.05/2.31  tff(c_296, plain, (![A_18, B_19]: (k4_xboole_0(k4_xboole_0(A_18, B_19), A_18)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_281])).
% 6.05/2.31  tff(c_36, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.05/2.31  tff(c_200, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_36, c_188])).
% 6.05/2.31  tff(c_970, plain, (![A_80, B_81, C_82]: (k4_xboole_0(k3_xboole_0(A_80, B_81), C_82)=k3_xboole_0(A_80, k4_xboole_0(B_81, C_82)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.05/2.31  tff(c_2228, plain, (![C_109]: (k3_xboole_0('#skF_1', k4_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_109))=k4_xboole_0('#skF_1', C_109))), inference(superposition, [status(thm), theory('equality')], [c_200, c_970])).
% 6.05/2.31  tff(c_2270, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_296, c_2228])).
% 6.05/2.31  tff(c_2280, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_219, c_2270])).
% 6.05/2.31  tff(c_2282, plain, $false, inference(negUnitSimplification, [status(thm)], [c_209, c_2280])).
% 6.05/2.31  tff(c_2283, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_34])).
% 6.05/2.31  tff(c_2432, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_2428, c_2283])).
% 6.05/2.31  tff(c_24, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k2_xboole_0(A_20, B_21))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.05/2.31  tff(c_18, plain, (![A_14, B_15]: (k3_xboole_0(A_14, k2_xboole_0(A_14, B_15))=A_14)), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.05/2.31  tff(c_2539, plain, (![A_132, B_133]: (k5_xboole_0(A_132, k3_xboole_0(A_132, B_133))=k4_xboole_0(A_132, B_133))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.05/2.31  tff(c_2564, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k2_xboole_0(A_14, B_15))=k5_xboole_0(A_14, A_14))), inference(superposition, [status(thm), theory('equality')], [c_18, c_2539])).
% 6.05/2.31  tff(c_2582, plain, (![A_14]: (k5_xboole_0(A_14, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2564])).
% 6.05/2.31  tff(c_2284, plain, (r1_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_34])).
% 6.05/2.31  tff(c_2341, plain, (![A_117, B_118]: (k3_xboole_0(A_117, B_118)=A_117 | ~r1_tarski(A_117, B_118))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.05/2.31  tff(c_2355, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_2284, c_2341])).
% 6.05/2.31  tff(c_3238, plain, (![A_155, B_156, C_157]: (k4_xboole_0(k3_xboole_0(A_155, B_156), C_157)=k3_xboole_0(A_155, k4_xboole_0(B_156, C_157)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.05/2.31  tff(c_5141, plain, (![C_189]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_189))=k4_xboole_0('#skF_1', C_189))), inference(superposition, [status(thm), theory('equality')], [c_2355, c_3238])).
% 6.05/2.31  tff(c_2357, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_36, c_2341])).
% 6.05/2.31  tff(c_5165, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_5141, c_2357])).
% 6.05/2.31  tff(c_14, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.05/2.31  tff(c_47, plain, (![B_34, A_35]: (k5_xboole_0(B_34, A_35)=k5_xboole_0(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.05/2.31  tff(c_28, plain, (![A_25]: (k5_xboole_0(A_25, k1_xboole_0)=A_25)), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.05/2.31  tff(c_63, plain, (![A_35]: (k5_xboole_0(k1_xboole_0, A_35)=A_35)), inference(superposition, [status(thm), theory('equality')], [c_47, c_28])).
% 6.05/2.31  tff(c_2998, plain, (![A_148, B_149, C_150]: (k5_xboole_0(k5_xboole_0(A_148, B_149), C_150)=k5_xboole_0(A_148, k5_xboole_0(B_149, C_150)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.05/2.31  tff(c_3042, plain, (![A_14, C_150]: (k5_xboole_0(A_14, k5_xboole_0(A_14, C_150))=k5_xboole_0(k1_xboole_0, C_150))), inference(superposition, [status(thm), theory('equality')], [c_2582, c_2998])).
% 6.05/2.31  tff(c_3087, plain, (![A_151, C_152]: (k5_xboole_0(A_151, k5_xboole_0(A_151, C_152))=C_152)), inference(demodulation, [status(thm), theory('equality')], [c_63, c_3042])).
% 6.05/2.31  tff(c_8011, plain, (![A_219, B_220]: (k5_xboole_0(A_219, k4_xboole_0(A_219, B_220))=k3_xboole_0(A_219, B_220))), inference(superposition, [status(thm), theory('equality')], [c_14, c_3087])).
% 6.05/2.31  tff(c_8071, plain, (k5_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5165, c_8011])).
% 6.05/2.31  tff(c_8125, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2582, c_8071])).
% 6.05/2.31  tff(c_8127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2432, c_8125])).
% 6.05/2.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.05/2.31  
% 6.05/2.31  Inference rules
% 6.05/2.31  ----------------------
% 6.05/2.31  #Ref     : 0
% 6.05/2.31  #Sup     : 2061
% 6.05/2.31  #Fact    : 0
% 6.05/2.31  #Define  : 0
% 6.05/2.31  #Split   : 2
% 6.05/2.31  #Chain   : 0
% 6.05/2.31  #Close   : 0
% 6.05/2.31  
% 6.05/2.31  Ordering : KBO
% 6.05/2.31  
% 6.05/2.31  Simplification rules
% 6.05/2.31  ----------------------
% 6.05/2.31  #Subsume      : 54
% 6.05/2.31  #Demod        : 1625
% 6.05/2.31  #Tautology    : 1196
% 6.05/2.31  #SimpNegUnit  : 2
% 6.05/2.31  #BackRed      : 5
% 6.05/2.31  
% 6.05/2.31  #Partial instantiations: 0
% 6.05/2.31  #Strategies tried      : 1
% 6.05/2.31  
% 6.05/2.31  Timing (in seconds)
% 6.05/2.31  ----------------------
% 6.05/2.31  Preprocessing        : 0.31
% 6.05/2.31  Parsing              : 0.17
% 6.05/2.32  CNF conversion       : 0.02
% 6.05/2.32  Main loop            : 1.19
% 6.05/2.32  Inferencing          : 0.34
% 6.05/2.32  Reduction            : 0.58
% 6.05/2.32  Demodulation         : 0.49
% 6.05/2.32  BG Simplification    : 0.04
% 6.05/2.32  Subsumption          : 0.17
% 6.05/2.32  Abstraction          : 0.06
% 6.05/2.32  MUC search           : 0.00
% 6.05/2.32  Cooper               : 0.00
% 6.05/2.32  Total                : 1.54
% 6.05/2.32  Index Insertion      : 0.00
% 6.05/2.32  Index Deletion       : 0.00
% 6.05/2.32  Index Matching       : 0.00
% 6.05/2.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
