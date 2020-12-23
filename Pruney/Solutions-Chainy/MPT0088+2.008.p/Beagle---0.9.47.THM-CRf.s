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
% DateTime   : Thu Dec  3 09:44:21 EST 2020

% Result     : Theorem 4.60s
% Output     : CNFRefutation 4.60s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 104 expanded)
%              Number of leaves         :   23 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :   57 (  99 expanded)
%              Number of equality atoms :   49 (  88 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,k4_xboole_0(B,C))
       => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).

tff(c_87,plain,(
    ! [A_30,B_31] :
      ( r1_xboole_0(A_30,B_31)
      | k3_xboole_0(A_30,B_31) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ~ r1_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_95,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_87,c_26])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_96,plain,(
    ! [A_32,B_33] : k4_xboole_0(A_32,k4_xboole_0(A_32,B_33)) = k3_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_111,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_96])).

tff(c_114,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_111])).

tff(c_115,plain,(
    ! [A_34] : k4_xboole_0(A_34,A_34) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_111])).

tff(c_16,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_120,plain,(
    ! [A_34] : k4_xboole_0(A_34,k1_xboole_0) = k3_xboole_0(A_34,A_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_16])).

tff(c_132,plain,(
    ! [A_34] : k3_xboole_0(A_34,A_34) = A_34 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_120])).

tff(c_552,plain,(
    ! [A_51,B_52,C_53] : k4_xboole_0(k3_xboole_0(A_51,B_52),C_53) = k3_xboole_0(A_51,k4_xboole_0(B_52,C_53)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_791,plain,(
    ! [A_59,C_60] : k3_xboole_0(A_59,k4_xboole_0(A_59,C_60)) = k4_xboole_0(A_59,C_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_552])).

tff(c_22,plain,(
    ! [A_19,B_20] : k2_xboole_0(k3_xboole_0(A_19,B_20),k4_xboole_0(A_19,B_20)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_340,plain,(
    ! [A_43,B_44] : k4_xboole_0(A_43,k3_xboole_0(A_43,B_44)) = k4_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_346,plain,(
    ! [A_43,B_44] : k2_xboole_0(k3_xboole_0(A_43,B_44),k4_xboole_0(A_43,B_44)) = k2_xboole_0(k3_xboole_0(A_43,B_44),A_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_340,c_10])).

tff(c_366,plain,(
    ! [A_43,B_44] : k2_xboole_0(A_43,k3_xboole_0(A_43,B_44)) = A_43 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2,c_346])).

tff(c_820,plain,(
    ! [A_59,C_60] : k2_xboole_0(A_59,k4_xboole_0(A_59,C_60)) = A_59 ),
    inference(superposition,[status(thm),theory(equality)],[c_791,c_366])).

tff(c_1243,plain,(
    ! [A_68,B_69,C_70] : k2_xboole_0(k4_xboole_0(A_68,B_69),k3_xboole_0(A_68,C_70)) = k4_xboole_0(A_68,k4_xboole_0(B_69,C_70)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1297,plain,(
    ! [A_34,B_69] : k4_xboole_0(A_34,k4_xboole_0(B_69,A_34)) = k2_xboole_0(k4_xboole_0(A_34,B_69),A_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_1243])).

tff(c_1338,plain,(
    ! [A_71,B_72] : k4_xboole_0(A_71,k4_xboole_0(B_72,A_71)) = A_71 ),
    inference(demodulation,[status(thm),theory(equality)],[c_820,c_2,c_1297])).

tff(c_1382,plain,(
    ! [A_71,B_72] : k3_xboole_0(A_71,k4_xboole_0(B_72,A_71)) = k4_xboole_0(A_71,A_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_1338,c_16])).

tff(c_1448,plain,(
    ! [A_71,B_72] : k3_xboole_0(A_71,k4_xboole_0(B_72,A_71)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_1382])).

tff(c_14,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28,plain,(
    r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_78,plain,(
    ! [A_28,B_29] :
      ( k3_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_xboole_0(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_82,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_78])).

tff(c_702,plain,(
    ! [A_56,B_57,C_58] : k4_xboole_0(k3_xboole_0(A_56,B_57),k3_xboole_0(A_56,C_58)) = k3_xboole_0(A_56,k4_xboole_0(B_57,C_58)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_766,plain,(
    ! [B_57] : k3_xboole_0('#skF_1',k4_xboole_0(B_57,k4_xboole_0('#skF_2','#skF_3'))) = k4_xboole_0(k3_xboole_0('#skF_1',B_57),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_702])).

tff(c_1668,plain,(
    ! [B_77] : k3_xboole_0('#skF_1',k4_xboole_0(B_77,k4_xboole_0('#skF_2','#skF_3'))) = k3_xboole_0('#skF_1',B_77) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_766])).

tff(c_1743,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1668])).

tff(c_1834,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1743,c_14])).

tff(c_1848,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1834])).

tff(c_18,plain,(
    ! [A_13,B_14,C_15] : k4_xboole_0(k3_xboole_0(A_13,B_14),C_15) = k3_xboole_0(A_13,k4_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5856,plain,(
    ! [A_122,B_123,C_124] : k3_xboole_0(A_122,k4_xboole_0(B_123,k3_xboole_0(A_122,C_124))) = k3_xboole_0(A_122,k4_xboole_0(B_123,C_124)) ),
    inference(superposition,[status(thm),theory(equality)],[c_702,c_18])).

tff(c_6046,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1848,c_5856])).

tff(c_6170,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1448,c_6046])).

tff(c_6172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_6170])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:55:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.60/1.95  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.60/1.96  
% 4.60/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.60/1.96  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.60/1.96  
% 4.60/1.96  %Foreground sorts:
% 4.60/1.96  
% 4.60/1.96  
% 4.60/1.96  %Background operators:
% 4.60/1.96  
% 4.60/1.96  
% 4.60/1.96  %Foreground operators:
% 4.60/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.60/1.96  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.60/1.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.60/1.96  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.60/1.96  tff('#skF_2', type, '#skF_2': $i).
% 4.60/1.96  tff('#skF_3', type, '#skF_3': $i).
% 4.60/1.96  tff('#skF_1', type, '#skF_1': $i).
% 4.60/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.60/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.60/1.96  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.60/1.96  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.60/1.96  
% 4.60/1.98  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.60/1.98  tff(f_54, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_xboole_1)).
% 4.60/1.98  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 4.60/1.98  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.60/1.98  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.60/1.98  tff(f_43, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 4.60/1.98  tff(f_47, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 4.60/1.98  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.60/1.98  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.60/1.98  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.60/1.98  tff(f_49, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 4.60/1.98  tff(f_45, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_xboole_1)).
% 4.60/1.98  tff(c_87, plain, (![A_30, B_31]: (r1_xboole_0(A_30, B_31) | k3_xboole_0(A_30, B_31)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.60/1.98  tff(c_26, plain, (~r1_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.60/1.98  tff(c_95, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_87, c_26])).
% 4.60/1.98  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.60/1.98  tff(c_12, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.60/1.98  tff(c_96, plain, (![A_32, B_33]: (k4_xboole_0(A_32, k4_xboole_0(A_32, B_33))=k3_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.60/1.98  tff(c_111, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_96])).
% 4.60/1.98  tff(c_114, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_111])).
% 4.60/1.98  tff(c_115, plain, (![A_34]: (k4_xboole_0(A_34, A_34)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_111])).
% 4.60/1.98  tff(c_16, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.60/1.98  tff(c_120, plain, (![A_34]: (k4_xboole_0(A_34, k1_xboole_0)=k3_xboole_0(A_34, A_34))), inference(superposition, [status(thm), theory('equality')], [c_115, c_16])).
% 4.60/1.98  tff(c_132, plain, (![A_34]: (k3_xboole_0(A_34, A_34)=A_34)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_120])).
% 4.60/1.98  tff(c_552, plain, (![A_51, B_52, C_53]: (k4_xboole_0(k3_xboole_0(A_51, B_52), C_53)=k3_xboole_0(A_51, k4_xboole_0(B_52, C_53)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.60/1.98  tff(c_791, plain, (![A_59, C_60]: (k3_xboole_0(A_59, k4_xboole_0(A_59, C_60))=k4_xboole_0(A_59, C_60))), inference(superposition, [status(thm), theory('equality')], [c_132, c_552])).
% 4.60/1.98  tff(c_22, plain, (![A_19, B_20]: (k2_xboole_0(k3_xboole_0(A_19, B_20), k4_xboole_0(A_19, B_20))=A_19)), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.60/1.98  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.60/1.98  tff(c_340, plain, (![A_43, B_44]: (k4_xboole_0(A_43, k3_xboole_0(A_43, B_44))=k4_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.60/1.98  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.60/1.98  tff(c_346, plain, (![A_43, B_44]: (k2_xboole_0(k3_xboole_0(A_43, B_44), k4_xboole_0(A_43, B_44))=k2_xboole_0(k3_xboole_0(A_43, B_44), A_43))), inference(superposition, [status(thm), theory('equality')], [c_340, c_10])).
% 4.60/1.98  tff(c_366, plain, (![A_43, B_44]: (k2_xboole_0(A_43, k3_xboole_0(A_43, B_44))=A_43)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2, c_346])).
% 4.60/1.98  tff(c_820, plain, (![A_59, C_60]: (k2_xboole_0(A_59, k4_xboole_0(A_59, C_60))=A_59)), inference(superposition, [status(thm), theory('equality')], [c_791, c_366])).
% 4.60/1.98  tff(c_1243, plain, (![A_68, B_69, C_70]: (k2_xboole_0(k4_xboole_0(A_68, B_69), k3_xboole_0(A_68, C_70))=k4_xboole_0(A_68, k4_xboole_0(B_69, C_70)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.60/1.98  tff(c_1297, plain, (![A_34, B_69]: (k4_xboole_0(A_34, k4_xboole_0(B_69, A_34))=k2_xboole_0(k4_xboole_0(A_34, B_69), A_34))), inference(superposition, [status(thm), theory('equality')], [c_132, c_1243])).
% 4.60/1.98  tff(c_1338, plain, (![A_71, B_72]: (k4_xboole_0(A_71, k4_xboole_0(B_72, A_71))=A_71)), inference(demodulation, [status(thm), theory('equality')], [c_820, c_2, c_1297])).
% 4.60/1.98  tff(c_1382, plain, (![A_71, B_72]: (k3_xboole_0(A_71, k4_xboole_0(B_72, A_71))=k4_xboole_0(A_71, A_71))), inference(superposition, [status(thm), theory('equality')], [c_1338, c_16])).
% 4.60/1.98  tff(c_1448, plain, (![A_71, B_72]: (k3_xboole_0(A_71, k4_xboole_0(B_72, A_71))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_114, c_1382])).
% 4.60/1.98  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.60/1.98  tff(c_28, plain, (r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.60/1.98  tff(c_78, plain, (![A_28, B_29]: (k3_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.60/1.98  tff(c_82, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_78])).
% 4.60/1.98  tff(c_702, plain, (![A_56, B_57, C_58]: (k4_xboole_0(k3_xboole_0(A_56, B_57), k3_xboole_0(A_56, C_58))=k3_xboole_0(A_56, k4_xboole_0(B_57, C_58)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.60/1.98  tff(c_766, plain, (![B_57]: (k3_xboole_0('#skF_1', k4_xboole_0(B_57, k4_xboole_0('#skF_2', '#skF_3')))=k4_xboole_0(k3_xboole_0('#skF_1', B_57), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_82, c_702])).
% 4.60/1.98  tff(c_1668, plain, (![B_77]: (k3_xboole_0('#skF_1', k4_xboole_0(B_77, k4_xboole_0('#skF_2', '#skF_3')))=k3_xboole_0('#skF_1', B_77))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_766])).
% 4.60/1.98  tff(c_1743, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_16, c_1668])).
% 4.60/1.98  tff(c_1834, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1743, c_14])).
% 4.60/1.98  tff(c_1848, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1834])).
% 4.60/1.98  tff(c_18, plain, (![A_13, B_14, C_15]: (k4_xboole_0(k3_xboole_0(A_13, B_14), C_15)=k3_xboole_0(A_13, k4_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.60/1.98  tff(c_5856, plain, (![A_122, B_123, C_124]: (k3_xboole_0(A_122, k4_xboole_0(B_123, k3_xboole_0(A_122, C_124)))=k3_xboole_0(A_122, k4_xboole_0(B_123, C_124)))), inference(superposition, [status(thm), theory('equality')], [c_702, c_18])).
% 4.60/1.98  tff(c_6046, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1848, c_5856])).
% 4.60/1.98  tff(c_6170, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1448, c_6046])).
% 4.60/1.98  tff(c_6172, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_6170])).
% 4.60/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.60/1.98  
% 4.60/1.98  Inference rules
% 4.60/1.98  ----------------------
% 4.60/1.98  #Ref     : 0
% 4.60/1.98  #Sup     : 1558
% 4.60/1.98  #Fact    : 0
% 4.60/1.98  #Define  : 0
% 4.60/1.98  #Split   : 0
% 4.60/1.98  #Chain   : 0
% 4.60/1.98  #Close   : 0
% 4.60/1.98  
% 4.60/1.98  Ordering : KBO
% 4.60/1.98  
% 4.60/1.98  Simplification rules
% 4.60/1.98  ----------------------
% 4.60/1.98  #Subsume      : 0
% 4.60/1.98  #Demod        : 1432
% 4.60/1.98  #Tautology    : 1053
% 4.60/1.98  #SimpNegUnit  : 1
% 4.60/1.98  #BackRed      : 1
% 4.60/1.98  
% 4.60/1.98  #Partial instantiations: 0
% 4.60/1.98  #Strategies tried      : 1
% 4.60/1.98  
% 4.60/1.98  Timing (in seconds)
% 4.60/1.98  ----------------------
% 4.60/1.98  Preprocessing        : 0.31
% 4.60/1.98  Parsing              : 0.17
% 4.60/1.98  CNF conversion       : 0.02
% 4.60/1.98  Main loop            : 0.86
% 4.60/1.98  Inferencing          : 0.26
% 4.60/1.98  Reduction            : 0.41
% 4.60/1.98  Demodulation         : 0.34
% 4.60/1.98  BG Simplification    : 0.03
% 4.60/1.98  Subsumption          : 0.11
% 4.60/1.98  Abstraction          : 0.05
% 4.60/1.98  MUC search           : 0.00
% 4.60/1.98  Cooper               : 0.00
% 4.60/1.98  Total                : 1.20
% 4.60/1.98  Index Insertion      : 0.00
% 4.60/1.98  Index Deletion       : 0.00
% 4.60/1.98  Index Matching       : 0.00
% 4.60/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
