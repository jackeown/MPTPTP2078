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
% DateTime   : Thu Dec  3 09:45:17 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 135 expanded)
%              Number of leaves         :   22 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :   60 ( 149 expanded)
%              Number of equality atoms :   31 (  93 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_xboole_1)).

tff(c_261,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(A_42,B_43)
      | k4_xboole_0(A_42,B_43) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_78,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_269,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_261,c_78])).

tff(c_16,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [A_14,B_15] : r1_tarski(k4_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_270,plain,(
    ! [A_44,B_45] :
      ( k4_xboole_0(A_44,B_45) = k1_xboole_0
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_296,plain,(
    ! [A_14,B_15] : k4_xboole_0(k4_xboole_0(A_14,B_15),A_14) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_270])).

tff(c_28,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_215,plain,(
    ! [A_39,B_40] :
      ( k3_xboole_0(A_39,B_40) = A_39
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_241,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_28,c_215])).

tff(c_626,plain,(
    ! [A_60,B_61,C_62] : k4_xboole_0(k3_xboole_0(A_60,B_61),C_62) = k3_xboole_0(A_60,k4_xboole_0(B_61,C_62)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_853,plain,(
    ! [C_67] : k3_xboole_0('#skF_1',k4_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_67)) = k4_xboole_0('#skF_1',C_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_626])).

tff(c_893,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_853])).

tff(c_909,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_893])).

tff(c_911,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_269,c_909])).

tff(c_912,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_1029,plain,(
    ! [A_74,B_75] :
      ( k3_xboole_0(A_74,B_75) = A_74
      | ~ r1_tarski(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1055,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_28,c_1029])).

tff(c_22,plain,(
    ! [A_17,B_18,C_19] : k4_xboole_0(k3_xboole_0(A_17,B_18),C_19) = k3_xboole_0(A_17,k4_xboole_0(B_18,C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1214,plain,(
    ! [A_86,B_87] : k5_xboole_0(A_86,k3_xboole_0(A_86,B_87)) = k4_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1241,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = k4_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1214])).

tff(c_1247,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1241])).

tff(c_12,plain,(
    ! [A_9,B_10] : r1_tarski(k3_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1117,plain,(
    ! [A_81,B_82] :
      ( k4_xboole_0(A_81,B_82) = k1_xboole_0
      | ~ r1_tarski(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1422,plain,(
    ! [A_95,B_96] : k4_xboole_0(k3_xboole_0(A_95,B_96),A_95) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_1117])).

tff(c_1586,plain,(
    ! [A_100,B_101] : k3_xboole_0(A_100,k4_xboole_0(B_101,A_100)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1422,c_22])).

tff(c_10,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1600,plain,(
    ! [A_100,B_101] : k4_xboole_0(A_100,k4_xboole_0(B_101,A_100)) = k5_xboole_0(A_100,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1586,c_10])).

tff(c_1646,plain,(
    ! [A_100,B_101] : k4_xboole_0(A_100,k4_xboole_0(B_101,A_100)) = A_100 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1247,c_1600])).

tff(c_1663,plain,(
    ! [A_102,B_103] : k4_xboole_0(A_102,k4_xboole_0(B_103,A_102)) = A_102 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1247,c_1600])).

tff(c_24,plain,(
    ! [A_20,B_21] : r1_xboole_0(k4_xboole_0(A_20,B_21),k4_xboole_0(B_21,A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1950,plain,(
    ! [B_108,A_109] : r1_xboole_0(k4_xboole_0(k4_xboole_0(B_108,A_109),A_109),A_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_1663,c_24])).

tff(c_1953,plain,(
    ! [A_100,B_101] : r1_xboole_0(k4_xboole_0(A_100,k4_xboole_0(B_101,A_100)),k4_xboole_0(B_101,A_100)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1646,c_1950])).

tff(c_2001,plain,(
    ! [A_110,B_111] : r1_xboole_0(A_110,k4_xboole_0(B_111,A_110)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1646,c_1953])).

tff(c_2100,plain,(
    ! [B_113,A_114] : r1_xboole_0(k4_xboole_0(B_113,A_114),A_114) ),
    inference(superposition,[status(thm),theory(equality)],[c_1646,c_2001])).

tff(c_2216,plain,(
    ! [A_118,B_119,C_120] : r1_xboole_0(k3_xboole_0(A_118,k4_xboole_0(B_119,C_120)),C_120) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2100])).

tff(c_2259,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1055,c_2216])).

tff(c_2289,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_912,c_2259])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:17:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.96/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.51  
% 2.96/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.51  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.96/1.51  
% 2.96/1.51  %Foreground sorts:
% 2.96/1.51  
% 2.96/1.51  
% 2.96/1.51  %Background operators:
% 2.96/1.51  
% 2.96/1.51  
% 2.96/1.51  %Foreground operators:
% 2.96/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.96/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.96/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.96/1.51  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.96/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.96/1.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.96/1.51  tff('#skF_2', type, '#skF_2': $i).
% 2.96/1.51  tff('#skF_3', type, '#skF_3': $i).
% 2.96/1.51  tff('#skF_1', type, '#skF_1': $i).
% 2.96/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.96/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.96/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.96/1.51  
% 2.96/1.52  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.96/1.52  tff(f_58, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.96/1.52  tff(f_43, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.96/1.52  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.96/1.52  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.96/1.52  tff(f_49, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.96/1.52  tff(f_47, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.96/1.52  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.96/1.52  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.96/1.52  tff(f_51, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_xboole_1)).
% 2.96/1.52  tff(c_261, plain, (![A_42, B_43]: (r1_tarski(A_42, B_43) | k4_xboole_0(A_42, B_43)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.96/1.52  tff(c_26, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.96/1.52  tff(c_78, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_26])).
% 2.96/1.52  tff(c_269, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_261, c_78])).
% 2.96/1.52  tff(c_16, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.96/1.52  tff(c_18, plain, (![A_14, B_15]: (r1_tarski(k4_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.96/1.52  tff(c_270, plain, (![A_44, B_45]: (k4_xboole_0(A_44, B_45)=k1_xboole_0 | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.96/1.52  tff(c_296, plain, (![A_14, B_15]: (k4_xboole_0(k4_xboole_0(A_14, B_15), A_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_270])).
% 2.96/1.52  tff(c_28, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.96/1.52  tff(c_215, plain, (![A_39, B_40]: (k3_xboole_0(A_39, B_40)=A_39 | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.96/1.52  tff(c_241, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_28, c_215])).
% 2.96/1.52  tff(c_626, plain, (![A_60, B_61, C_62]: (k4_xboole_0(k3_xboole_0(A_60, B_61), C_62)=k3_xboole_0(A_60, k4_xboole_0(B_61, C_62)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.96/1.52  tff(c_853, plain, (![C_67]: (k3_xboole_0('#skF_1', k4_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_67))=k4_xboole_0('#skF_1', C_67))), inference(superposition, [status(thm), theory('equality')], [c_241, c_626])).
% 2.96/1.52  tff(c_893, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_296, c_853])).
% 2.96/1.52  tff(c_909, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_893])).
% 2.96/1.52  tff(c_911, plain, $false, inference(negUnitSimplification, [status(thm)], [c_269, c_909])).
% 2.96/1.52  tff(c_912, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_26])).
% 2.96/1.52  tff(c_1029, plain, (![A_74, B_75]: (k3_xboole_0(A_74, B_75)=A_74 | ~r1_tarski(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.96/1.52  tff(c_1055, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_28, c_1029])).
% 2.96/1.52  tff(c_22, plain, (![A_17, B_18, C_19]: (k4_xboole_0(k3_xboole_0(A_17, B_18), C_19)=k3_xboole_0(A_17, k4_xboole_0(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.96/1.52  tff(c_20, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.96/1.52  tff(c_1214, plain, (![A_86, B_87]: (k5_xboole_0(A_86, k3_xboole_0(A_86, B_87))=k4_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.96/1.52  tff(c_1241, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=k4_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1214])).
% 2.96/1.52  tff(c_1247, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1241])).
% 2.96/1.52  tff(c_12, plain, (![A_9, B_10]: (r1_tarski(k3_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.96/1.52  tff(c_1117, plain, (![A_81, B_82]: (k4_xboole_0(A_81, B_82)=k1_xboole_0 | ~r1_tarski(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.96/1.52  tff(c_1422, plain, (![A_95, B_96]: (k4_xboole_0(k3_xboole_0(A_95, B_96), A_95)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_1117])).
% 2.96/1.52  tff(c_1586, plain, (![A_100, B_101]: (k3_xboole_0(A_100, k4_xboole_0(B_101, A_100))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1422, c_22])).
% 2.96/1.52  tff(c_10, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.96/1.52  tff(c_1600, plain, (![A_100, B_101]: (k4_xboole_0(A_100, k4_xboole_0(B_101, A_100))=k5_xboole_0(A_100, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1586, c_10])).
% 2.96/1.52  tff(c_1646, plain, (![A_100, B_101]: (k4_xboole_0(A_100, k4_xboole_0(B_101, A_100))=A_100)), inference(demodulation, [status(thm), theory('equality')], [c_1247, c_1600])).
% 2.96/1.52  tff(c_1663, plain, (![A_102, B_103]: (k4_xboole_0(A_102, k4_xboole_0(B_103, A_102))=A_102)), inference(demodulation, [status(thm), theory('equality')], [c_1247, c_1600])).
% 2.96/1.52  tff(c_24, plain, (![A_20, B_21]: (r1_xboole_0(k4_xboole_0(A_20, B_21), k4_xboole_0(B_21, A_20)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.96/1.52  tff(c_1950, plain, (![B_108, A_109]: (r1_xboole_0(k4_xboole_0(k4_xboole_0(B_108, A_109), A_109), A_109))), inference(superposition, [status(thm), theory('equality')], [c_1663, c_24])).
% 2.96/1.52  tff(c_1953, plain, (![A_100, B_101]: (r1_xboole_0(k4_xboole_0(A_100, k4_xboole_0(B_101, A_100)), k4_xboole_0(B_101, A_100)))), inference(superposition, [status(thm), theory('equality')], [c_1646, c_1950])).
% 2.96/1.52  tff(c_2001, plain, (![A_110, B_111]: (r1_xboole_0(A_110, k4_xboole_0(B_111, A_110)))), inference(demodulation, [status(thm), theory('equality')], [c_1646, c_1953])).
% 2.96/1.52  tff(c_2100, plain, (![B_113, A_114]: (r1_xboole_0(k4_xboole_0(B_113, A_114), A_114))), inference(superposition, [status(thm), theory('equality')], [c_1646, c_2001])).
% 2.96/1.52  tff(c_2216, plain, (![A_118, B_119, C_120]: (r1_xboole_0(k3_xboole_0(A_118, k4_xboole_0(B_119, C_120)), C_120))), inference(superposition, [status(thm), theory('equality')], [c_22, c_2100])).
% 2.96/1.52  tff(c_2259, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1055, c_2216])).
% 2.96/1.52  tff(c_2289, plain, $false, inference(negUnitSimplification, [status(thm)], [c_912, c_2259])).
% 2.96/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.52  
% 2.96/1.52  Inference rules
% 2.96/1.52  ----------------------
% 2.96/1.52  #Ref     : 0
% 2.96/1.52  #Sup     : 560
% 2.96/1.52  #Fact    : 0
% 2.96/1.52  #Define  : 0
% 2.96/1.52  #Split   : 1
% 2.96/1.52  #Chain   : 0
% 2.96/1.52  #Close   : 0
% 2.96/1.52  
% 2.96/1.52  Ordering : KBO
% 2.96/1.52  
% 2.96/1.52  Simplification rules
% 2.96/1.52  ----------------------
% 2.96/1.52  #Subsume      : 0
% 2.96/1.52  #Demod        : 373
% 2.96/1.52  #Tautology    : 432
% 2.96/1.52  #SimpNegUnit  : 2
% 2.96/1.52  #BackRed      : 4
% 2.96/1.52  
% 2.96/1.52  #Partial instantiations: 0
% 2.96/1.52  #Strategies tried      : 1
% 2.96/1.52  
% 2.96/1.52  Timing (in seconds)
% 2.96/1.52  ----------------------
% 2.96/1.53  Preprocessing        : 0.28
% 2.96/1.53  Parsing              : 0.15
% 2.96/1.53  CNF conversion       : 0.02
% 2.96/1.53  Main loop            : 0.46
% 2.96/1.53  Inferencing          : 0.16
% 2.96/1.53  Reduction            : 0.18
% 2.96/1.53  Demodulation         : 0.15
% 2.96/1.53  BG Simplification    : 0.02
% 2.96/1.53  Subsumption          : 0.06
% 2.96/1.53  Abstraction          : 0.02
% 2.96/1.53  MUC search           : 0.00
% 2.96/1.53  Cooper               : 0.00
% 2.96/1.53  Total                : 0.77
% 2.96/1.53  Index Insertion      : 0.00
% 2.96/1.53  Index Deletion       : 0.00
% 2.96/1.53  Index Matching       : 0.00
% 2.96/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
