%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:20 EST 2020

% Result     : Theorem 4.56s
% Output     : CNFRefutation 4.56s
% Verified   : 
% Statistics : Number of formulae       :   58 (  72 expanded)
%              Number of leaves         :   23 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :   51 (  67 expanded)
%              Number of equality atoms :   43 (  56 expanded)
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

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).

tff(c_87,plain,(
    ! [A_29,B_30] :
      ( r1_xboole_0(A_29,B_30)
      | k3_xboole_0(A_29,B_30) != k1_xboole_0 ) ),
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

tff(c_339,plain,(
    ! [A_43,B_44] : k4_xboole_0(A_43,k4_xboole_0(A_43,B_44)) = k3_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_377,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k3_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_339])).

tff(c_388,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_377])).

tff(c_24,plain,(
    ! [A_21,B_22] : k2_xboole_0(k3_xboole_0(A_21,B_22),k4_xboole_0(A_21,B_22)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_203,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k3_xboole_0(A_37,B_38)) = k4_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_209,plain,(
    ! [A_37,B_38] : k2_xboole_0(k3_xboole_0(A_37,B_38),k4_xboole_0(A_37,B_38)) = k2_xboole_0(k3_xboole_0(A_37,B_38),A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_10])).

tff(c_223,plain,(
    ! [A_37,B_38] : k2_xboole_0(A_37,k3_xboole_0(A_37,B_38)) = A_37 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2,c_209])).

tff(c_499,plain,(
    ! [A_48,B_49] : k4_xboole_0(k2_xboole_0(A_48,B_49),B_49) = k4_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_863,plain,(
    ! [B_60,A_61] : k4_xboole_0(k2_xboole_0(B_60,A_61),B_60) = k4_xboole_0(A_61,B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_499])).

tff(c_905,plain,(
    ! [A_37,B_38] : k4_xboole_0(k3_xboole_0(A_37,B_38),A_37) = k4_xboole_0(A_37,A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_863])).

tff(c_945,plain,(
    ! [A_62,B_63] : k4_xboole_0(k3_xboole_0(A_62,B_63),A_62) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_905])).

tff(c_20,plain,(
    ! [A_15,B_16,C_17] : k4_xboole_0(k3_xboole_0(A_15,B_16),C_17) = k3_xboole_0(A_15,k4_xboole_0(B_16,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_956,plain,(
    ! [A_62,B_63] : k3_xboole_0(A_62,k4_xboole_0(B_63,A_62)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_945,c_20])).

tff(c_16,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_28,plain,(
    r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_78,plain,(
    ! [A_27,B_28] :
      ( k3_xboole_0(A_27,B_28) = k1_xboole_0
      | ~ r1_xboole_0(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_82,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_78])).

tff(c_1197,plain,(
    ! [A_68,B_69,C_70] : k4_xboole_0(k3_xboole_0(A_68,B_69),k3_xboole_0(A_68,C_70)) = k3_xboole_0(A_68,k4_xboole_0(B_69,C_70)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1281,plain,(
    ! [B_69] : k3_xboole_0('#skF_1',k4_xboole_0(B_69,k4_xboole_0('#skF_2','#skF_3'))) = k4_xboole_0(k3_xboole_0('#skF_1',B_69),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_1197])).

tff(c_1462,plain,(
    ! [B_73] : k3_xboole_0('#skF_1',k4_xboole_0(B_73,k4_xboole_0('#skF_2','#skF_3'))) = k3_xboole_0('#skF_1',B_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1281])).

tff(c_1540,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1462])).

tff(c_2085,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1540,c_16])).

tff(c_2098,plain,(
    k4_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2085])).

tff(c_1215,plain,(
    ! [A_68,B_69,C_70] : k3_xboole_0(A_68,k4_xboole_0(B_69,k3_xboole_0(A_68,C_70))) = k3_xboole_0(A_68,k4_xboole_0(B_69,C_70)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1197,c_20])).

tff(c_5990,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2098,c_1215])).

tff(c_6039,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_956,c_5990])).

tff(c_6041,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_6039])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:04:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.56/1.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.56/1.88  
% 4.56/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.56/1.88  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.56/1.88  
% 4.56/1.88  %Foreground sorts:
% 4.56/1.88  
% 4.56/1.88  
% 4.56/1.88  %Background operators:
% 4.56/1.88  
% 4.56/1.88  
% 4.56/1.88  %Foreground operators:
% 4.56/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.56/1.88  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.56/1.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.56/1.88  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.56/1.88  tff('#skF_2', type, '#skF_2': $i).
% 4.56/1.88  tff('#skF_3', type, '#skF_3': $i).
% 4.56/1.88  tff('#skF_1', type, '#skF_1': $i).
% 4.56/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.56/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.56/1.88  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.56/1.88  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.56/1.88  
% 4.56/1.90  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.56/1.90  tff(f_54, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_xboole_1)).
% 4.56/1.90  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 4.56/1.90  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.56/1.90  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.56/1.90  tff(f_49, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 4.56/1.90  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.56/1.90  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.56/1.90  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.56/1.90  tff(f_39, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 4.56/1.90  tff(f_45, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 4.56/1.90  tff(f_47, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_xboole_1)).
% 4.56/1.90  tff(c_87, plain, (![A_29, B_30]: (r1_xboole_0(A_29, B_30) | k3_xboole_0(A_29, B_30)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.56/1.90  tff(c_26, plain, (~r1_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.56/1.90  tff(c_95, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_87, c_26])).
% 4.56/1.90  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.56/1.90  tff(c_12, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.56/1.90  tff(c_339, plain, (![A_43, B_44]: (k4_xboole_0(A_43, k4_xboole_0(A_43, B_44))=k3_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.56/1.90  tff(c_377, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k3_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_339])).
% 4.56/1.90  tff(c_388, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_377])).
% 4.56/1.90  tff(c_24, plain, (![A_21, B_22]: (k2_xboole_0(k3_xboole_0(A_21, B_22), k4_xboole_0(A_21, B_22))=A_21)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.56/1.90  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.56/1.90  tff(c_203, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k3_xboole_0(A_37, B_38))=k4_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.56/1.90  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.56/1.90  tff(c_209, plain, (![A_37, B_38]: (k2_xboole_0(k3_xboole_0(A_37, B_38), k4_xboole_0(A_37, B_38))=k2_xboole_0(k3_xboole_0(A_37, B_38), A_37))), inference(superposition, [status(thm), theory('equality')], [c_203, c_10])).
% 4.56/1.90  tff(c_223, plain, (![A_37, B_38]: (k2_xboole_0(A_37, k3_xboole_0(A_37, B_38))=A_37)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2, c_209])).
% 4.56/1.90  tff(c_499, plain, (![A_48, B_49]: (k4_xboole_0(k2_xboole_0(A_48, B_49), B_49)=k4_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.56/1.90  tff(c_863, plain, (![B_60, A_61]: (k4_xboole_0(k2_xboole_0(B_60, A_61), B_60)=k4_xboole_0(A_61, B_60))), inference(superposition, [status(thm), theory('equality')], [c_2, c_499])).
% 4.56/1.90  tff(c_905, plain, (![A_37, B_38]: (k4_xboole_0(k3_xboole_0(A_37, B_38), A_37)=k4_xboole_0(A_37, A_37))), inference(superposition, [status(thm), theory('equality')], [c_223, c_863])).
% 4.56/1.90  tff(c_945, plain, (![A_62, B_63]: (k4_xboole_0(k3_xboole_0(A_62, B_63), A_62)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_388, c_905])).
% 4.56/1.90  tff(c_20, plain, (![A_15, B_16, C_17]: (k4_xboole_0(k3_xboole_0(A_15, B_16), C_17)=k3_xboole_0(A_15, k4_xboole_0(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.56/1.90  tff(c_956, plain, (![A_62, B_63]: (k3_xboole_0(A_62, k4_xboole_0(B_63, A_62))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_945, c_20])).
% 4.56/1.90  tff(c_16, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.56/1.90  tff(c_18, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.56/1.90  tff(c_28, plain, (r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.56/1.90  tff(c_78, plain, (![A_27, B_28]: (k3_xboole_0(A_27, B_28)=k1_xboole_0 | ~r1_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.56/1.90  tff(c_82, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_78])).
% 4.56/1.90  tff(c_1197, plain, (![A_68, B_69, C_70]: (k4_xboole_0(k3_xboole_0(A_68, B_69), k3_xboole_0(A_68, C_70))=k3_xboole_0(A_68, k4_xboole_0(B_69, C_70)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.56/1.90  tff(c_1281, plain, (![B_69]: (k3_xboole_0('#skF_1', k4_xboole_0(B_69, k4_xboole_0('#skF_2', '#skF_3')))=k4_xboole_0(k3_xboole_0('#skF_1', B_69), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_82, c_1197])).
% 4.56/1.90  tff(c_1462, plain, (![B_73]: (k3_xboole_0('#skF_1', k4_xboole_0(B_73, k4_xboole_0('#skF_2', '#skF_3')))=k3_xboole_0('#skF_1', B_73))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1281])).
% 4.56/1.90  tff(c_1540, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_18, c_1462])).
% 4.56/1.90  tff(c_2085, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1540, c_16])).
% 4.56/1.90  tff(c_2098, plain, (k4_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2085])).
% 4.56/1.90  tff(c_1215, plain, (![A_68, B_69, C_70]: (k3_xboole_0(A_68, k4_xboole_0(B_69, k3_xboole_0(A_68, C_70)))=k3_xboole_0(A_68, k4_xboole_0(B_69, C_70)))), inference(superposition, [status(thm), theory('equality')], [c_1197, c_20])).
% 4.56/1.90  tff(c_5990, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2098, c_1215])).
% 4.56/1.90  tff(c_6039, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_956, c_5990])).
% 4.56/1.90  tff(c_6041, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_6039])).
% 4.56/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.56/1.90  
% 4.56/1.90  Inference rules
% 4.56/1.90  ----------------------
% 4.56/1.90  #Ref     : 0
% 4.56/1.90  #Sup     : 1508
% 4.56/1.90  #Fact    : 0
% 4.56/1.90  #Define  : 0
% 4.56/1.90  #Split   : 0
% 4.56/1.90  #Chain   : 0
% 4.56/1.90  #Close   : 0
% 4.56/1.90  
% 4.56/1.90  Ordering : KBO
% 4.56/1.90  
% 4.56/1.90  Simplification rules
% 4.56/1.90  ----------------------
% 4.56/1.90  #Subsume      : 3
% 4.56/1.90  #Demod        : 1661
% 4.56/1.90  #Tautology    : 1117
% 4.56/1.90  #SimpNegUnit  : 1
% 4.56/1.90  #BackRed      : 1
% 4.56/1.90  
% 4.56/1.90  #Partial instantiations: 0
% 4.56/1.90  #Strategies tried      : 1
% 4.56/1.90  
% 4.56/1.90  Timing (in seconds)
% 4.56/1.90  ----------------------
% 4.56/1.90  Preprocessing        : 0.29
% 4.56/1.90  Parsing              : 0.16
% 4.56/1.90  CNF conversion       : 0.02
% 4.56/1.90  Main loop            : 0.82
% 4.56/1.90  Inferencing          : 0.25
% 4.56/1.90  Reduction            : 0.40
% 4.56/1.90  Demodulation         : 0.34
% 4.56/1.90  BG Simplification    : 0.03
% 4.56/1.90  Subsumption          : 0.10
% 4.56/1.90  Abstraction          : 0.05
% 4.56/1.90  MUC search           : 0.00
% 4.56/1.90  Cooper               : 0.00
% 4.56/1.90  Total                : 1.13
% 4.56/1.90  Index Insertion      : 0.00
% 4.56/1.90  Index Deletion       : 0.00
% 4.56/1.90  Index Matching       : 0.00
% 4.56/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
