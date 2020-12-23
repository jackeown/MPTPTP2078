%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:13 EST 2020

% Result     : Theorem 5.37s
% Output     : CNFRefutation 5.37s
% Verified   : 
% Statistics : Number of formulae       :   60 (  73 expanded)
%              Number of leaves         :   24 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   58 (  84 expanded)
%              Number of equality atoms :   32 (  38 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_53,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_51,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_1868,plain,(
    ! [A_96,B_97] :
      ( r1_xboole_0(A_96,B_97)
      | k3_xboole_0(A_96,B_97) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_89,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_28,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_188,plain,(
    ! [A_35,B_36] :
      ( k3_xboole_0(A_35,B_36) = A_35
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_196,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_28,c_188])).

tff(c_18,plain,(
    ! [A_16,B_17,C_18] : k4_xboole_0(k3_xboole_0(A_16,B_17),C_18) = k3_xboole_0(A_16,k4_xboole_0(B_17,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_14,B_15] : r1_tarski(k4_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_206,plain,(
    ! [A_39,B_40,C_41] :
      ( r1_tarski(A_39,B_40)
      | ~ r1_tarski(A_39,k3_xboole_0(B_40,C_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_221,plain,(
    ! [B_42,C_43,B_44] : r1_tarski(k4_xboole_0(k3_xboole_0(B_42,C_43),B_44),B_42) ),
    inference(resolution,[status(thm)],[c_16,c_206])).

tff(c_234,plain,(
    ! [B_2,A_1,B_44] : r1_tarski(k4_xboole_0(k3_xboole_0(B_2,A_1),B_44),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_221])).

tff(c_1693,plain,(
    ! [B_90,A_91,B_92] : r1_tarski(k3_xboole_0(B_90,k4_xboole_0(A_91,B_92)),A_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_234])).

tff(c_1748,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_1693])).

tff(c_1771,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_1748])).

tff(c_1772,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_1872,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1868,c_1772])).

tff(c_24,plain,(
    ! [A_23] : k5_xboole_0(A_23,A_23) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1773,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_1881,plain,(
    ! [A_100,B_101] :
      ( k3_xboole_0(A_100,B_101) = A_100
      | ~ r1_tarski(A_100,B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1891,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1773,c_1881])).

tff(c_1996,plain,(
    ! [A_107,B_108,C_109] : k4_xboole_0(k3_xboole_0(A_107,B_108),C_109) = k3_xboole_0(A_107,k4_xboole_0(B_108,C_109)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2511,plain,(
    ! [C_126] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_126)) = k4_xboole_0('#skF_1',C_126) ),
    inference(superposition,[status(thm),theory(equality)],[c_1891,c_1996])).

tff(c_1893,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_28,c_1881])).

tff(c_2529,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_2511,c_1893])).

tff(c_10,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1774,plain,(
    ! [B_93,A_94] : k5_xboole_0(B_93,A_94) = k5_xboole_0(A_94,B_93) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1790,plain,(
    ! [A_94] : k5_xboole_0(k1_xboole_0,A_94) = A_94 ),
    inference(superposition,[status(thm),theory(equality)],[c_1774,c_20])).

tff(c_2097,plain,(
    ! [A_111,B_112,C_113] : k5_xboole_0(k5_xboole_0(A_111,B_112),C_113) = k5_xboole_0(A_111,k5_xboole_0(B_112,C_113)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2161,plain,(
    ! [A_23,C_113] : k5_xboole_0(A_23,k5_xboole_0(A_23,C_113)) = k5_xboole_0(k1_xboole_0,C_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2097])).

tff(c_2191,plain,(
    ! [A_114,C_115] : k5_xboole_0(A_114,k5_xboole_0(A_114,C_115)) = C_115 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1790,c_2161])).

tff(c_6564,plain,(
    ! [A_215,B_216] : k5_xboole_0(A_215,k4_xboole_0(A_215,B_216)) = k3_xboole_0(A_215,B_216) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2191])).

tff(c_6643,plain,(
    k5_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2529,c_6564])).

tff(c_6672,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_6643])).

tff(c_6674,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1872,c_6672])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:41:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.37/2.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.37/2.02  
% 5.37/2.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.37/2.02  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.37/2.02  
% 5.37/2.02  %Foreground sorts:
% 5.37/2.02  
% 5.37/2.02  
% 5.37/2.02  %Background operators:
% 5.37/2.02  
% 5.37/2.02  
% 5.37/2.02  %Foreground operators:
% 5.37/2.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.37/2.02  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.37/2.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.37/2.02  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.37/2.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.37/2.02  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.37/2.02  tff('#skF_2', type, '#skF_2': $i).
% 5.37/2.02  tff('#skF_3', type, '#skF_3': $i).
% 5.37/2.02  tff('#skF_1', type, '#skF_1': $i).
% 5.37/2.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.37/2.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.37/2.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.37/2.02  
% 5.37/2.03  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.37/2.03  tff(f_60, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 5.37/2.03  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.37/2.03  tff(f_47, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 5.37/2.03  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.37/2.03  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.37/2.03  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 5.37/2.03  tff(f_53, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 5.37/2.03  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.37/2.03  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 5.37/2.03  tff(f_49, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 5.37/2.03  tff(f_51, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.37/2.03  tff(c_1868, plain, (![A_96, B_97]: (r1_xboole_0(A_96, B_97) | k3_xboole_0(A_96, B_97)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.37/2.03  tff(c_26, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.37/2.03  tff(c_89, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_26])).
% 5.37/2.03  tff(c_28, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.37/2.03  tff(c_188, plain, (![A_35, B_36]: (k3_xboole_0(A_35, B_36)=A_35 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.37/2.03  tff(c_196, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_28, c_188])).
% 5.37/2.03  tff(c_18, plain, (![A_16, B_17, C_18]: (k4_xboole_0(k3_xboole_0(A_16, B_17), C_18)=k3_xboole_0(A_16, k4_xboole_0(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.37/2.03  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.37/2.03  tff(c_16, plain, (![A_14, B_15]: (r1_tarski(k4_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.37/2.03  tff(c_206, plain, (![A_39, B_40, C_41]: (r1_tarski(A_39, B_40) | ~r1_tarski(A_39, k3_xboole_0(B_40, C_41)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.37/2.03  tff(c_221, plain, (![B_42, C_43, B_44]: (r1_tarski(k4_xboole_0(k3_xboole_0(B_42, C_43), B_44), B_42))), inference(resolution, [status(thm)], [c_16, c_206])).
% 5.37/2.03  tff(c_234, plain, (![B_2, A_1, B_44]: (r1_tarski(k4_xboole_0(k3_xboole_0(B_2, A_1), B_44), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_221])).
% 5.37/2.03  tff(c_1693, plain, (![B_90, A_91, B_92]: (r1_tarski(k3_xboole_0(B_90, k4_xboole_0(A_91, B_92)), A_91))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_234])).
% 5.37/2.03  tff(c_1748, plain, (r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_196, c_1693])).
% 5.37/2.03  tff(c_1771, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89, c_1748])).
% 5.37/2.03  tff(c_1772, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_26])).
% 5.37/2.03  tff(c_1872, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_1868, c_1772])).
% 5.37/2.03  tff(c_24, plain, (![A_23]: (k5_xboole_0(A_23, A_23)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.37/2.03  tff(c_1773, plain, (r1_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_26])).
% 5.37/2.03  tff(c_1881, plain, (![A_100, B_101]: (k3_xboole_0(A_100, B_101)=A_100 | ~r1_tarski(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.37/2.03  tff(c_1891, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_1773, c_1881])).
% 5.37/2.03  tff(c_1996, plain, (![A_107, B_108, C_109]: (k4_xboole_0(k3_xboole_0(A_107, B_108), C_109)=k3_xboole_0(A_107, k4_xboole_0(B_108, C_109)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.37/2.03  tff(c_2511, plain, (![C_126]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_126))=k4_xboole_0('#skF_1', C_126))), inference(superposition, [status(thm), theory('equality')], [c_1891, c_1996])).
% 5.37/2.03  tff(c_1893, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_28, c_1881])).
% 5.37/2.03  tff(c_2529, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_2511, c_1893])).
% 5.37/2.03  tff(c_10, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.37/2.03  tff(c_1774, plain, (![B_93, A_94]: (k5_xboole_0(B_93, A_94)=k5_xboole_0(A_94, B_93))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.37/2.03  tff(c_20, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.37/2.03  tff(c_1790, plain, (![A_94]: (k5_xboole_0(k1_xboole_0, A_94)=A_94)), inference(superposition, [status(thm), theory('equality')], [c_1774, c_20])).
% 5.37/2.03  tff(c_2097, plain, (![A_111, B_112, C_113]: (k5_xboole_0(k5_xboole_0(A_111, B_112), C_113)=k5_xboole_0(A_111, k5_xboole_0(B_112, C_113)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.37/2.03  tff(c_2161, plain, (![A_23, C_113]: (k5_xboole_0(A_23, k5_xboole_0(A_23, C_113))=k5_xboole_0(k1_xboole_0, C_113))), inference(superposition, [status(thm), theory('equality')], [c_24, c_2097])).
% 5.37/2.03  tff(c_2191, plain, (![A_114, C_115]: (k5_xboole_0(A_114, k5_xboole_0(A_114, C_115))=C_115)), inference(demodulation, [status(thm), theory('equality')], [c_1790, c_2161])).
% 5.37/2.03  tff(c_6564, plain, (![A_215, B_216]: (k5_xboole_0(A_215, k4_xboole_0(A_215, B_216))=k3_xboole_0(A_215, B_216))), inference(superposition, [status(thm), theory('equality')], [c_10, c_2191])).
% 5.37/2.03  tff(c_6643, plain, (k5_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2529, c_6564])).
% 5.37/2.03  tff(c_6672, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_6643])).
% 5.37/2.03  tff(c_6674, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1872, c_6672])).
% 5.37/2.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.37/2.03  
% 5.37/2.03  Inference rules
% 5.37/2.03  ----------------------
% 5.37/2.03  #Ref     : 0
% 5.37/2.03  #Sup     : 1664
% 5.37/2.03  #Fact    : 0
% 5.37/2.03  #Define  : 0
% 5.37/2.03  #Split   : 1
% 5.37/2.03  #Chain   : 0
% 5.37/2.03  #Close   : 0
% 5.37/2.03  
% 5.37/2.03  Ordering : KBO
% 5.37/2.03  
% 5.37/2.03  Simplification rules
% 5.37/2.03  ----------------------
% 5.37/2.03  #Subsume      : 50
% 5.37/2.03  #Demod        : 1161
% 5.37/2.03  #Tautology    : 1040
% 5.37/2.03  #SimpNegUnit  : 2
% 5.37/2.03  #BackRed      : 7
% 5.37/2.03  
% 5.37/2.03  #Partial instantiations: 0
% 5.37/2.03  #Strategies tried      : 1
% 5.37/2.03  
% 5.37/2.03  Timing (in seconds)
% 5.37/2.03  ----------------------
% 5.37/2.03  Preprocessing        : 0.28
% 5.37/2.03  Parsing              : 0.15
% 5.37/2.03  CNF conversion       : 0.02
% 5.37/2.03  Main loop            : 1.01
% 5.37/2.03  Inferencing          : 0.31
% 5.37/2.03  Reduction            : 0.45
% 5.37/2.03  Demodulation         : 0.38
% 5.37/2.03  BG Simplification    : 0.03
% 5.37/2.03  Subsumption          : 0.14
% 5.37/2.03  Abstraction          : 0.05
% 5.37/2.03  MUC search           : 0.00
% 5.37/2.03  Cooper               : 0.00
% 5.37/2.03  Total                : 1.32
% 5.37/2.03  Index Insertion      : 0.00
% 5.37/2.04  Index Deletion       : 0.00
% 5.37/2.04  Index Matching       : 0.00
% 5.37/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
