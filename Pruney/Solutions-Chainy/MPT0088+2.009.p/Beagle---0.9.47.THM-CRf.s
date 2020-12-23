%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:21 EST 2020

% Result     : Theorem 14.02s
% Output     : CNFRefutation 14.02s
% Verified   : 
% Statistics : Number of formulae       :   66 (  88 expanded)
%              Number of leaves         :   26 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :   66 ( 102 expanded)
%              Number of equality atoms :   33 (  48 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,k4_xboole_0(B,C))
       => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_59,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_69,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_55,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_53,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_28,plain,(
    ~ r1_xboole_0('#skF_4',k4_xboole_0('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_16,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_47,plain,(
    ! [A_30,B_31] : r1_xboole_0(k4_xboole_0(A_30,B_31),B_31) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_50,plain,(
    ! [A_15] : r1_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_47])).

tff(c_12,plain,(
    ! [A_12] : k3_xboole_0(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_217,plain,(
    ! [A_47,B_48,C_49] :
      ( ~ r1_xboole_0(A_47,B_48)
      | ~ r2_hidden(C_49,k3_xboole_0(A_47,B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_224,plain,(
    ! [A_12,C_49] :
      ( ~ r1_xboole_0(A_12,k1_xboole_0)
      | ~ r2_hidden(C_49,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_217])).

tff(c_227,plain,(
    ! [C_49] : ~ r2_hidden(C_49,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_224])).

tff(c_901,plain,(
    ! [A_75,B_76,C_77] : k4_xboole_0(k4_xboole_0(A_75,B_76),C_77) = k4_xboole_0(A_75,k2_xboole_0(B_76,C_77)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_20,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_926,plain,(
    ! [A_75,B_76,C_77] : k4_xboole_0(k4_xboole_0(A_75,B_76),k4_xboole_0(A_75,k2_xboole_0(B_76,C_77))) = k3_xboole_0(k4_xboole_0(A_75,B_76),C_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_901,c_20])).

tff(c_14,plain,(
    ! [A_13,B_14] : k2_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_13945,plain,(
    ! [A_236,B_237,C_238] : k4_xboole_0(k4_xboole_0(A_236,B_237),k4_xboole_0(A_236,k2_xboole_0(B_237,C_238))) = k3_xboole_0(k4_xboole_0(A_236,B_237),C_238) ),
    inference(superposition,[status(thm),theory(equality)],[c_901,c_20])).

tff(c_14289,plain,(
    ! [A_236,A_13,B_14] : k4_xboole_0(k4_xboole_0(A_236,A_13),k4_xboole_0(A_236,k2_xboole_0(A_13,B_14))) = k3_xboole_0(k4_xboole_0(A_236,A_13),k4_xboole_0(B_14,A_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_13945])).

tff(c_57906,plain,(
    ! [A_483,A_484,B_485] : k3_xboole_0(k4_xboole_0(A_483,A_484),k4_xboole_0(B_485,A_484)) = k3_xboole_0(k4_xboole_0(A_483,A_484),B_485) ),
    inference(demodulation,[status(thm),theory(equality)],[c_926,c_14289])).

tff(c_30,plain,(
    r1_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_236,plain,(
    ! [A_51,B_52] :
      ( ~ r1_xboole_0(A_51,B_52)
      | k3_xboole_0(A_51,B_52) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_217])).

tff(c_261,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_236])).

tff(c_22,plain,(
    ! [A_21,B_22] : k2_xboole_0(k3_xboole_0(A_21,B_22),k4_xboole_0(A_21,B_22)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_458,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5'))) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_22])).

tff(c_114,plain,(
    ! [A_41,B_42] : k2_xboole_0(k3_xboole_0(A_41,B_42),k4_xboole_0(A_41,B_42)) = A_41 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_123,plain,(
    ! [A_12] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_12,k1_xboole_0)) = A_12 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_114])).

tff(c_129,plain,(
    ! [A_12] : k2_xboole_0(k1_xboole_0,A_12) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_123])).

tff(c_715,plain,(
    k4_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_129])).

tff(c_8526,plain,(
    ! [C_198] : k4_xboole_0('#skF_3',k2_xboole_0(k4_xboole_0('#skF_4','#skF_5'),C_198)) = k4_xboole_0('#skF_3',C_198) ),
    inference(superposition,[status(thm),theory(equality)],[c_715,c_901])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_26,plain,(
    ! [A_26,B_27] : r1_xboole_0(k4_xboole_0(A_26,B_27),B_27) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1970,plain,(
    ! [A_98,B_99,C_100] : r1_xboole_0(k4_xboole_0(A_98,k2_xboole_0(B_99,C_100)),C_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_901,c_26])).

tff(c_225,plain,(
    ! [A_47,B_48] :
      ( ~ r1_xboole_0(A_47,B_48)
      | k3_xboole_0(A_47,B_48) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_217])).

tff(c_4542,plain,(
    ! [A_154,B_155,C_156] : k3_xboole_0(k4_xboole_0(A_154,k2_xboole_0(B_155,C_156)),C_156) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1970,c_225])).

tff(c_4664,plain,(
    ! [A_154,B_2,A_1] : k3_xboole_0(k4_xboole_0(A_154,k2_xboole_0(B_2,A_1)),B_2) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4542])).

tff(c_8559,plain,(
    ! [C_198] : k3_xboole_0(k4_xboole_0('#skF_3',C_198),k4_xboole_0('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8526,c_4664])).

tff(c_57976,plain,(
    k3_xboole_0(k4_xboole_0('#skF_3','#skF_5'),'#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_57906,c_8559])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),k3_xboole_0(A_5,B_6))
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_58912,plain,
    ( r2_hidden('#skF_1'(k4_xboole_0('#skF_3','#skF_5'),'#skF_4'),k1_xboole_0)
    | r1_xboole_0(k4_xboole_0('#skF_3','#skF_5'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_57976,c_6])).

tff(c_58978,plain,(
    r1_xboole_0(k4_xboole_0('#skF_3','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_227,c_58912])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58985,plain,(
    r1_xboole_0('#skF_4',k4_xboole_0('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_58978,c_4])).

tff(c_58991,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_58985])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:03:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.02/7.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.02/7.78  
% 14.02/7.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.02/7.78  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 14.02/7.78  
% 14.02/7.78  %Foreground sorts:
% 14.02/7.78  
% 14.02/7.78  
% 14.02/7.78  %Background operators:
% 14.02/7.78  
% 14.02/7.78  
% 14.02/7.78  %Foreground operators:
% 14.02/7.78  tff('#skF_2', type, '#skF_2': $i > $i).
% 14.02/7.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.02/7.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.02/7.78  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.02/7.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.02/7.78  tff('#skF_5', type, '#skF_5': $i).
% 14.02/7.78  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 14.02/7.78  tff('#skF_3', type, '#skF_3': $i).
% 14.02/7.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.02/7.78  tff('#skF_4', type, '#skF_4': $i).
% 14.02/7.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.02/7.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.02/7.78  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.02/7.78  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 14.02/7.78  
% 14.02/7.79  tff(f_74, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_xboole_1)).
% 14.02/7.79  tff(f_59, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 14.02/7.79  tff(f_69, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 14.02/7.79  tff(f_55, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 14.02/7.79  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 14.02/7.79  tff(f_61, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 14.02/7.79  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 14.02/7.79  tff(f_57, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 14.02/7.79  tff(f_53, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 14.02/7.79  tff(f_65, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 14.02/7.79  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 14.02/7.79  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 14.02/7.79  tff(c_28, plain, (~r1_xboole_0('#skF_4', k4_xboole_0('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 14.02/7.80  tff(c_16, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_59])).
% 14.02/7.80  tff(c_47, plain, (![A_30, B_31]: (r1_xboole_0(k4_xboole_0(A_30, B_31), B_31))), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.02/7.80  tff(c_50, plain, (![A_15]: (r1_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_47])).
% 14.02/7.80  tff(c_12, plain, (![A_12]: (k3_xboole_0(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 14.02/7.80  tff(c_217, plain, (![A_47, B_48, C_49]: (~r1_xboole_0(A_47, B_48) | ~r2_hidden(C_49, k3_xboole_0(A_47, B_48)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.02/7.80  tff(c_224, plain, (![A_12, C_49]: (~r1_xboole_0(A_12, k1_xboole_0) | ~r2_hidden(C_49, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_217])).
% 14.02/7.80  tff(c_227, plain, (![C_49]: (~r2_hidden(C_49, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_224])).
% 14.02/7.80  tff(c_901, plain, (![A_75, B_76, C_77]: (k4_xboole_0(k4_xboole_0(A_75, B_76), C_77)=k4_xboole_0(A_75, k2_xboole_0(B_76, C_77)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 14.02/7.80  tff(c_20, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 14.02/7.80  tff(c_926, plain, (![A_75, B_76, C_77]: (k4_xboole_0(k4_xboole_0(A_75, B_76), k4_xboole_0(A_75, k2_xboole_0(B_76, C_77)))=k3_xboole_0(k4_xboole_0(A_75, B_76), C_77))), inference(superposition, [status(thm), theory('equality')], [c_901, c_20])).
% 14.02/7.80  tff(c_14, plain, (![A_13, B_14]: (k2_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 14.02/7.80  tff(c_13945, plain, (![A_236, B_237, C_238]: (k4_xboole_0(k4_xboole_0(A_236, B_237), k4_xboole_0(A_236, k2_xboole_0(B_237, C_238)))=k3_xboole_0(k4_xboole_0(A_236, B_237), C_238))), inference(superposition, [status(thm), theory('equality')], [c_901, c_20])).
% 14.02/7.80  tff(c_14289, plain, (![A_236, A_13, B_14]: (k4_xboole_0(k4_xboole_0(A_236, A_13), k4_xboole_0(A_236, k2_xboole_0(A_13, B_14)))=k3_xboole_0(k4_xboole_0(A_236, A_13), k4_xboole_0(B_14, A_13)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_13945])).
% 14.02/7.80  tff(c_57906, plain, (![A_483, A_484, B_485]: (k3_xboole_0(k4_xboole_0(A_483, A_484), k4_xboole_0(B_485, A_484))=k3_xboole_0(k4_xboole_0(A_483, A_484), B_485))), inference(demodulation, [status(thm), theory('equality')], [c_926, c_14289])).
% 14.02/7.80  tff(c_30, plain, (r1_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 14.02/7.80  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_53])).
% 14.02/7.80  tff(c_236, plain, (![A_51, B_52]: (~r1_xboole_0(A_51, B_52) | k3_xboole_0(A_51, B_52)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_217])).
% 14.02/7.80  tff(c_261, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_236])).
% 14.02/7.80  tff(c_22, plain, (![A_21, B_22]: (k2_xboole_0(k3_xboole_0(A_21, B_22), k4_xboole_0(A_21, B_22))=A_21)), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.02/7.80  tff(c_458, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5')))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_261, c_22])).
% 14.02/7.80  tff(c_114, plain, (![A_41, B_42]: (k2_xboole_0(k3_xboole_0(A_41, B_42), k4_xboole_0(A_41, B_42))=A_41)), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.02/7.80  tff(c_123, plain, (![A_12]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_12, k1_xboole_0))=A_12)), inference(superposition, [status(thm), theory('equality')], [c_12, c_114])).
% 14.02/7.80  tff(c_129, plain, (![A_12]: (k2_xboole_0(k1_xboole_0, A_12)=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_123])).
% 14.02/7.80  tff(c_715, plain, (k4_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_458, c_129])).
% 14.02/7.80  tff(c_8526, plain, (![C_198]: (k4_xboole_0('#skF_3', k2_xboole_0(k4_xboole_0('#skF_4', '#skF_5'), C_198))=k4_xboole_0('#skF_3', C_198))), inference(superposition, [status(thm), theory('equality')], [c_715, c_901])).
% 14.02/7.80  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.02/7.80  tff(c_26, plain, (![A_26, B_27]: (r1_xboole_0(k4_xboole_0(A_26, B_27), B_27))), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.02/7.80  tff(c_1970, plain, (![A_98, B_99, C_100]: (r1_xboole_0(k4_xboole_0(A_98, k2_xboole_0(B_99, C_100)), C_100))), inference(superposition, [status(thm), theory('equality')], [c_901, c_26])).
% 14.02/7.80  tff(c_225, plain, (![A_47, B_48]: (~r1_xboole_0(A_47, B_48) | k3_xboole_0(A_47, B_48)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_217])).
% 14.02/7.80  tff(c_4542, plain, (![A_154, B_155, C_156]: (k3_xboole_0(k4_xboole_0(A_154, k2_xboole_0(B_155, C_156)), C_156)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1970, c_225])).
% 14.02/7.80  tff(c_4664, plain, (![A_154, B_2, A_1]: (k3_xboole_0(k4_xboole_0(A_154, k2_xboole_0(B_2, A_1)), B_2)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_4542])).
% 14.02/7.80  tff(c_8559, plain, (![C_198]: (k3_xboole_0(k4_xboole_0('#skF_3', C_198), k4_xboole_0('#skF_4', '#skF_5'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8526, c_4664])).
% 14.02/7.80  tff(c_57976, plain, (k3_xboole_0(k4_xboole_0('#skF_3', '#skF_5'), '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_57906, c_8559])).
% 14.02/7.80  tff(c_6, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), k3_xboole_0(A_5, B_6)) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.02/7.80  tff(c_58912, plain, (r2_hidden('#skF_1'(k4_xboole_0('#skF_3', '#skF_5'), '#skF_4'), k1_xboole_0) | r1_xboole_0(k4_xboole_0('#skF_3', '#skF_5'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_57976, c_6])).
% 14.02/7.80  tff(c_58978, plain, (r1_xboole_0(k4_xboole_0('#skF_3', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_227, c_58912])).
% 14.02/7.80  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.02/7.80  tff(c_58985, plain, (r1_xboole_0('#skF_4', k4_xboole_0('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_58978, c_4])).
% 14.02/7.80  tff(c_58991, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_58985])).
% 14.02/7.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.02/7.80  
% 14.02/7.80  Inference rules
% 14.02/7.80  ----------------------
% 14.02/7.80  #Ref     : 0
% 14.02/7.80  #Sup     : 14810
% 14.02/7.80  #Fact    : 0
% 14.02/7.80  #Define  : 0
% 14.02/7.80  #Split   : 0
% 14.02/7.80  #Chain   : 0
% 14.02/7.80  #Close   : 0
% 14.02/7.80  
% 14.02/7.80  Ordering : KBO
% 14.02/7.80  
% 14.02/7.80  Simplification rules
% 14.02/7.80  ----------------------
% 14.02/7.80  #Subsume      : 105
% 14.02/7.80  #Demod        : 17274
% 14.02/7.80  #Tautology    : 10095
% 14.02/7.80  #SimpNegUnit  : 37
% 14.02/7.80  #BackRed      : 3
% 14.02/7.80  
% 14.02/7.80  #Partial instantiations: 0
% 14.02/7.80  #Strategies tried      : 1
% 14.02/7.80  
% 14.02/7.80  Timing (in seconds)
% 14.02/7.80  ----------------------
% 14.02/7.80  Preprocessing        : 0.28
% 14.02/7.80  Parsing              : 0.16
% 14.02/7.80  CNF conversion       : 0.02
% 14.02/7.80  Main loop            : 6.73
% 14.02/7.80  Inferencing          : 0.94
% 14.02/7.80  Reduction            : 4.22
% 14.02/7.80  Demodulation         : 3.84
% 14.02/7.80  BG Simplification    : 0.12
% 14.02/7.80  Subsumption          : 1.17
% 14.02/7.80  Abstraction          : 0.21
% 14.02/7.80  MUC search           : 0.00
% 14.02/7.80  Cooper               : 0.00
% 14.02/7.80  Total                : 7.03
% 14.02/7.80  Index Insertion      : 0.00
% 14.02/7.80  Index Deletion       : 0.00
% 14.02/7.80  Index Matching       : 0.00
% 14.02/7.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
