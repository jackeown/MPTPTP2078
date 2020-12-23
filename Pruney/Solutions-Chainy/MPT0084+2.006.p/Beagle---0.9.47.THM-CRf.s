%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:05 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 152 expanded)
%              Number of leaves         :   25 (  61 expanded)
%              Depth                    :   26
%              Number of atoms          :   84 ( 223 expanded)
%              Number of equality atoms :   35 (  67 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_71,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_61,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_65,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_67,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_53,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(c_34,plain,(
    ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_28,plain,(
    ! [A_25] : r1_xboole_0(A_25,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_18,plain,(
    ! [A_17] : k3_xboole_0(A_17,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_372,plain,(
    ! [A_50,B_51,C_52] :
      ( ~ r1_xboole_0(A_50,B_51)
      | ~ r2_hidden(C_52,k3_xboole_0(A_50,B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_385,plain,(
    ! [A_17,C_52] :
      ( ~ r1_xboole_0(A_17,k1_xboole_0)
      | ~ r2_hidden(C_52,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_372])).

tff(c_388,plain,(
    ! [C_52] : ~ r2_hidden(C_52,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_385])).

tff(c_22,plain,(
    ! [A_20] : k4_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_116,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k4_xboole_0(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_134,plain,(
    ! [A_20] : k4_xboole_0(A_20,A_20) = k3_xboole_0(A_20,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_116])).

tff(c_162,plain,(
    ! [A_43] : k4_xboole_0(A_43,A_43) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_134])).

tff(c_24,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k4_xboole_0(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_170,plain,(
    ! [A_43] : k4_xboole_0(A_43,k1_xboole_0) = k3_xboole_0(A_43,A_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_24])).

tff(c_182,plain,(
    ! [A_43] : k3_xboole_0(A_43,A_43) = A_43 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_170])).

tff(c_642,plain,(
    ! [A_64,B_65,C_66] : k3_xboole_0(k3_xboole_0(A_64,B_65),C_66) = k3_xboole_0(A_64,k3_xboole_0(B_65,C_66)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_30,plain,(
    r1_xboole_0('#skF_3',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_86,plain,(
    ! [B_32,A_33] :
      ( r1_xboole_0(B_32,A_33)
      | ~ r1_xboole_0(A_33,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_91,plain,(
    r1_xboole_0(k3_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_86])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_407,plain,(
    ! [A_56,B_57] :
      ( ~ r1_xboole_0(A_56,B_57)
      | k3_xboole_0(A_56,B_57) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_372])).

tff(c_421,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_5'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_407])).

tff(c_654,plain,(
    k3_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_642,c_421])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),k3_xboole_0(A_5,B_6))
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_780,plain,
    ( r2_hidden('#skF_1'('#skF_4',k3_xboole_0('#skF_5','#skF_3')),k1_xboole_0)
    | r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_654,c_6])).

tff(c_791,plain,(
    r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_388,c_780])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_800,plain,(
    r1_xboole_0(k3_xboole_0('#skF_5','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_791,c_4])).

tff(c_386,plain,(
    ! [A_50,B_51] :
      ( ~ r1_xboole_0(A_50,B_51)
      | k3_xboole_0(A_50,B_51) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_372])).

tff(c_806,plain,(
    k3_xboole_0(k3_xboole_0('#skF_5','#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_800,c_386])).

tff(c_16,plain,(
    ! [A_14,B_15,C_16] : k3_xboole_0(k3_xboole_0(A_14,B_15),C_16) = k3_xboole_0(A_14,k3_xboole_0(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_819,plain,(
    k3_xboole_0('#skF_5',k3_xboole_0('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_806,c_16])).

tff(c_32,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_102,plain,(
    ! [A_35,B_36] :
      ( k4_xboole_0(A_35,B_36) = k1_xboole_0
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_106,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_102])).

tff(c_131,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k3_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_116])).

tff(c_137,plain,(
    k3_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_131])).

tff(c_1012,plain,(
    ! [C_71] : k3_xboole_0('#skF_3',k3_xboole_0('#skF_5',C_71)) = k3_xboole_0('#skF_3',C_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_642])).

tff(c_1039,plain,(
    k3_xboole_0('#skF_3',k3_xboole_0('#skF_3','#skF_4')) = k3_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_819,c_1012])).

tff(c_1052,plain,(
    k3_xboole_0('#skF_3',k3_xboole_0('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1039])).

tff(c_1067,plain,
    ( r2_hidden('#skF_1'('#skF_3',k3_xboole_0('#skF_3','#skF_4')),k1_xboole_0)
    | r1_xboole_0('#skF_3',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1052,c_6])).

tff(c_1079,plain,(
    r1_xboole_0('#skF_3',k3_xboole_0('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_388,c_1067])).

tff(c_1132,plain,(
    r1_xboole_0(k3_xboole_0('#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1079,c_4])).

tff(c_1138,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1132,c_386])).

tff(c_1187,plain,(
    k3_xboole_0('#skF_3',k3_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1138,c_16])).

tff(c_1222,plain,
    ( r2_hidden('#skF_1'('#skF_3',k3_xboole_0('#skF_4','#skF_3')),k1_xboole_0)
    | r1_xboole_0('#skF_3',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1187,c_6])).

tff(c_1233,plain,(
    r1_xboole_0('#skF_3',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_388,c_1222])).

tff(c_1242,plain,(
    r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1233,c_4])).

tff(c_1258,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_3'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1242,c_386])).

tff(c_1274,plain,(
    k3_xboole_0('#skF_4',k3_xboole_0('#skF_3','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1258,c_16])).

tff(c_1292,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_1274])).

tff(c_1319,plain,
    ( r2_hidden('#skF_1'('#skF_4','#skF_3'),k1_xboole_0)
    | r1_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1292,c_6])).

tff(c_1330,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_388,c_1319])).

tff(c_1336,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_1330,c_4])).

tff(c_1342,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1336])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:02:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.18/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.56  
% 3.18/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.56  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 3.18/1.56  
% 3.18/1.56  %Foreground sorts:
% 3.18/1.56  
% 3.18/1.56  
% 3.18/1.56  %Background operators:
% 3.18/1.56  
% 3.18/1.56  
% 3.18/1.56  %Foreground operators:
% 3.18/1.56  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.18/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.18/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.18/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.18/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.18/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.18/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.18/1.56  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.18/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.18/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.18/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.18/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.18/1.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.18/1.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.18/1.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.18/1.56  
% 3.18/1.57  tff(f_80, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_xboole_1)).
% 3.18/1.57  tff(f_71, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.18/1.57  tff(f_61, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.18/1.57  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.18/1.57  tff(f_65, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.18/1.57  tff(f_67, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.18/1.57  tff(f_59, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 3.18/1.57  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.18/1.57  tff(f_53, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.18/1.57  tff(f_57, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.18/1.57  tff(c_34, plain, (~r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.18/1.57  tff(c_28, plain, (![A_25]: (r1_xboole_0(A_25, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.18/1.57  tff(c_18, plain, (![A_17]: (k3_xboole_0(A_17, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.18/1.57  tff(c_372, plain, (![A_50, B_51, C_52]: (~r1_xboole_0(A_50, B_51) | ~r2_hidden(C_52, k3_xboole_0(A_50, B_51)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.18/1.57  tff(c_385, plain, (![A_17, C_52]: (~r1_xboole_0(A_17, k1_xboole_0) | ~r2_hidden(C_52, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_372])).
% 3.18/1.57  tff(c_388, plain, (![C_52]: (~r2_hidden(C_52, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_385])).
% 3.18/1.57  tff(c_22, plain, (![A_20]: (k4_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.18/1.57  tff(c_116, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k4_xboole_0(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.18/1.57  tff(c_134, plain, (![A_20]: (k4_xboole_0(A_20, A_20)=k3_xboole_0(A_20, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_116])).
% 3.18/1.57  tff(c_162, plain, (![A_43]: (k4_xboole_0(A_43, A_43)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_134])).
% 3.18/1.57  tff(c_24, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k4_xboole_0(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.18/1.57  tff(c_170, plain, (![A_43]: (k4_xboole_0(A_43, k1_xboole_0)=k3_xboole_0(A_43, A_43))), inference(superposition, [status(thm), theory('equality')], [c_162, c_24])).
% 3.18/1.57  tff(c_182, plain, (![A_43]: (k3_xboole_0(A_43, A_43)=A_43)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_170])).
% 3.18/1.57  tff(c_642, plain, (![A_64, B_65, C_66]: (k3_xboole_0(k3_xboole_0(A_64, B_65), C_66)=k3_xboole_0(A_64, k3_xboole_0(B_65, C_66)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.18/1.57  tff(c_30, plain, (r1_xboole_0('#skF_3', k3_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.18/1.57  tff(c_86, plain, (![B_32, A_33]: (r1_xboole_0(B_32, A_33) | ~r1_xboole_0(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.18/1.57  tff(c_91, plain, (r1_xboole_0(k3_xboole_0('#skF_4', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_30, c_86])).
% 3.18/1.57  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.18/1.57  tff(c_407, plain, (![A_56, B_57]: (~r1_xboole_0(A_56, B_57) | k3_xboole_0(A_56, B_57)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_372])).
% 3.18/1.57  tff(c_421, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_5'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_91, c_407])).
% 3.18/1.57  tff(c_654, plain, (k3_xboole_0('#skF_4', k3_xboole_0('#skF_5', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_642, c_421])).
% 3.18/1.57  tff(c_6, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), k3_xboole_0(A_5, B_6)) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.18/1.57  tff(c_780, plain, (r2_hidden('#skF_1'('#skF_4', k3_xboole_0('#skF_5', '#skF_3')), k1_xboole_0) | r1_xboole_0('#skF_4', k3_xboole_0('#skF_5', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_654, c_6])).
% 3.18/1.57  tff(c_791, plain, (r1_xboole_0('#skF_4', k3_xboole_0('#skF_5', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_388, c_780])).
% 3.18/1.57  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.18/1.57  tff(c_800, plain, (r1_xboole_0(k3_xboole_0('#skF_5', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_791, c_4])).
% 3.18/1.57  tff(c_386, plain, (![A_50, B_51]: (~r1_xboole_0(A_50, B_51) | k3_xboole_0(A_50, B_51)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_372])).
% 3.18/1.57  tff(c_806, plain, (k3_xboole_0(k3_xboole_0('#skF_5', '#skF_3'), '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_800, c_386])).
% 3.18/1.57  tff(c_16, plain, (![A_14, B_15, C_16]: (k3_xboole_0(k3_xboole_0(A_14, B_15), C_16)=k3_xboole_0(A_14, k3_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.18/1.57  tff(c_819, plain, (k3_xboole_0('#skF_5', k3_xboole_0('#skF_3', '#skF_4'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_806, c_16])).
% 3.18/1.57  tff(c_32, plain, (r1_tarski('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.18/1.57  tff(c_102, plain, (![A_35, B_36]: (k4_xboole_0(A_35, B_36)=k1_xboole_0 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.18/1.57  tff(c_106, plain, (k4_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_102])).
% 3.18/1.57  tff(c_131, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k3_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_106, c_116])).
% 3.18/1.57  tff(c_137, plain, (k3_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_131])).
% 3.18/1.57  tff(c_1012, plain, (![C_71]: (k3_xboole_0('#skF_3', k3_xboole_0('#skF_5', C_71))=k3_xboole_0('#skF_3', C_71))), inference(superposition, [status(thm), theory('equality')], [c_137, c_642])).
% 3.18/1.57  tff(c_1039, plain, (k3_xboole_0('#skF_3', k3_xboole_0('#skF_3', '#skF_4'))=k3_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_819, c_1012])).
% 3.18/1.57  tff(c_1052, plain, (k3_xboole_0('#skF_3', k3_xboole_0('#skF_3', '#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1039])).
% 3.18/1.57  tff(c_1067, plain, (r2_hidden('#skF_1'('#skF_3', k3_xboole_0('#skF_3', '#skF_4')), k1_xboole_0) | r1_xboole_0('#skF_3', k3_xboole_0('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1052, c_6])).
% 3.18/1.57  tff(c_1079, plain, (r1_xboole_0('#skF_3', k3_xboole_0('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_388, c_1067])).
% 3.18/1.57  tff(c_1132, plain, (r1_xboole_0(k3_xboole_0('#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_1079, c_4])).
% 3.18/1.57  tff(c_1138, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_4'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_1132, c_386])).
% 3.18/1.57  tff(c_1187, plain, (k3_xboole_0('#skF_3', k3_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1138, c_16])).
% 3.18/1.57  tff(c_1222, plain, (r2_hidden('#skF_1'('#skF_3', k3_xboole_0('#skF_4', '#skF_3')), k1_xboole_0) | r1_xboole_0('#skF_3', k3_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1187, c_6])).
% 3.18/1.57  tff(c_1233, plain, (r1_xboole_0('#skF_3', k3_xboole_0('#skF_4', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_388, c_1222])).
% 3.18/1.57  tff(c_1242, plain, (r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_1233, c_4])).
% 3.18/1.57  tff(c_1258, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_1242, c_386])).
% 3.18/1.57  tff(c_1274, plain, (k3_xboole_0('#skF_4', k3_xboole_0('#skF_3', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1258, c_16])).
% 3.18/1.57  tff(c_1292, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_182, c_1274])).
% 3.18/1.57  tff(c_1319, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_3'), k1_xboole_0) | r1_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1292, c_6])).
% 3.18/1.57  tff(c_1330, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_388, c_1319])).
% 3.18/1.57  tff(c_1336, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_1330, c_4])).
% 3.18/1.57  tff(c_1342, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_1336])).
% 3.18/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.57  
% 3.18/1.57  Inference rules
% 3.18/1.57  ----------------------
% 3.18/1.57  #Ref     : 0
% 3.18/1.57  #Sup     : 338
% 3.18/1.57  #Fact    : 0
% 3.18/1.57  #Define  : 0
% 3.18/1.57  #Split   : 1
% 3.18/1.57  #Chain   : 0
% 3.18/1.57  #Close   : 0
% 3.18/1.57  
% 3.18/1.57  Ordering : KBO
% 3.18/1.57  
% 3.18/1.57  Simplification rules
% 3.18/1.57  ----------------------
% 3.18/1.57  #Subsume      : 15
% 3.18/1.57  #Demod        : 263
% 3.18/1.57  #Tautology    : 207
% 3.18/1.57  #SimpNegUnit  : 16
% 3.18/1.57  #BackRed      : 7
% 3.18/1.57  
% 3.18/1.57  #Partial instantiations: 0
% 3.18/1.57  #Strategies tried      : 1
% 3.18/1.57  
% 3.18/1.57  Timing (in seconds)
% 3.18/1.57  ----------------------
% 3.18/1.57  Preprocessing        : 0.32
% 3.18/1.58  Parsing              : 0.17
% 3.18/1.58  CNF conversion       : 0.02
% 3.18/1.58  Main loop            : 0.44
% 3.18/1.58  Inferencing          : 0.14
% 3.18/1.58  Reduction            : 0.18
% 3.18/1.58  Demodulation         : 0.15
% 3.18/1.58  BG Simplification    : 0.02
% 3.18/1.58  Subsumption          : 0.07
% 3.18/1.58  Abstraction          : 0.02
% 3.18/1.58  MUC search           : 0.00
% 3.18/1.58  Cooper               : 0.00
% 3.18/1.58  Total                : 0.79
% 3.18/1.58  Index Insertion      : 0.00
% 3.18/1.58  Index Deletion       : 0.00
% 3.18/1.58  Index Matching       : 0.00
% 3.18/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
