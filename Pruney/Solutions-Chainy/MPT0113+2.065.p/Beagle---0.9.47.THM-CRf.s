%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:19 EST 2020

% Result     : Theorem 4.68s
% Output     : CNFRefutation 4.68s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 238 expanded)
%              Number of leaves         :   24 (  89 expanded)
%              Depth                    :   15
%              Number of atoms          :   77 ( 268 expanded)
%              Number of equality atoms :   46 ( 174 expanded)
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

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_22,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_51,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_24,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_306,plain,(
    ! [A_45,C_46,B_47] :
      ( r1_tarski(A_45,C_46)
      | ~ r1_tarski(B_47,C_46)
      | ~ r1_tarski(A_45,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_579,plain,(
    ! [A_59,A_60,B_61] :
      ( r1_tarski(A_59,A_60)
      | ~ r1_tarski(A_59,k4_xboole_0(A_60,B_61)) ) ),
    inference(resolution,[status(thm)],[c_10,c_306])).

tff(c_615,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_579])).

tff(c_632,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_615])).

tff(c_633,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_12,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_737,plain,(
    ! [A_70,B_71] : k5_xboole_0(A_70,k3_xboole_0(A_70,B_71)) = k4_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_755,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = k4_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_737])).

tff(c_759,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_755])).

tff(c_46,plain,(
    ! [A_26,B_27] : r1_tarski(k4_xboole_0(A_26,B_27),A_26) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_49,plain,(
    ! [A_11] : r1_tarski(A_11,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_46])).

tff(c_635,plain,(
    ! [A_62,B_63] :
      ( k3_xboole_0(A_62,B_63) = A_62
      | ~ r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_649,plain,(
    ! [A_11] : k3_xboole_0(A_11,A_11) = A_11 ),
    inference(resolution,[status(thm)],[c_49,c_635])).

tff(c_679,plain,(
    ! [A_65,B_66] : k4_xboole_0(A_65,k4_xboole_0(A_65,B_66)) = k3_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_700,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k3_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_679])).

tff(c_704,plain,(
    ! [A_67] : k4_xboole_0(A_67,A_67) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_700])).

tff(c_731,plain,(
    ! [A_68] : r1_tarski(k1_xboole_0,A_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_704,c_10])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_786,plain,(
    ! [A_74] : k3_xboole_0(k1_xboole_0,A_74) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_731,c_6])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_791,plain,(
    ! [A_74] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_786,c_2])).

tff(c_809,plain,(
    ! [A_74] : k4_xboole_0(k1_xboole_0,A_74) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_759,c_791])).

tff(c_1857,plain,(
    ! [A_119,B_120,C_121] : k2_xboole_0(k4_xboole_0(A_119,B_120),k3_xboole_0(A_119,C_121)) = k4_xboole_0(A_119,k4_xboole_0(B_120,C_121)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1914,plain,(
    ! [A_11,C_121] : k4_xboole_0(A_11,k4_xboole_0(k1_xboole_0,C_121)) = k2_xboole_0(A_11,k3_xboole_0(A_11,C_121)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1857])).

tff(c_1939,plain,(
    ! [A_122,C_123] : k2_xboole_0(A_122,k3_xboole_0(A_122,C_123)) = A_122 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_809,c_1914])).

tff(c_1963,plain,(
    ! [A_11] : k2_xboole_0(A_11,A_11) = A_11 ),
    inference(superposition,[status(thm),theory(equality)],[c_649,c_1939])).

tff(c_703,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_700])).

tff(c_746,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k4_xboole_0(A_11,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_649,c_737])).

tff(c_758,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_703,c_746])).

tff(c_1426,plain,(
    ! [A_103,B_104] : k5_xboole_0(k5_xboole_0(A_103,B_104),k2_xboole_0(A_103,B_104)) = k3_xboole_0(A_103,B_104) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1441,plain,(
    ! [A_11] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_11,A_11)) = k3_xboole_0(A_11,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_758,c_1426])).

tff(c_1450,plain,(
    ! [A_11] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_11,A_11)) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_649,c_1441])).

tff(c_2011,plain,(
    ! [A_11] : k5_xboole_0(k1_xboole_0,A_11) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1963,c_1450])).

tff(c_735,plain,(
    ! [A_68] : k3_xboole_0(k1_xboole_0,A_68) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_731,c_6])).

tff(c_634,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_648,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_634,c_635])).

tff(c_752,plain,(
    k5_xboole_0('#skF_1','#skF_1') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_648,c_737])).

tff(c_904,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_758,c_752])).

tff(c_650,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_24,c_635])).

tff(c_749,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k5_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_650,c_737])).

tff(c_815,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_758,c_749])).

tff(c_20,plain,(
    ! [A_19,B_20] : k5_xboole_0(k5_xboole_0(A_19,B_20),k2_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_5856,plain,(
    ! [A_205,B_206,C_207] : k5_xboole_0(k5_xboole_0(k4_xboole_0(A_205,B_206),k3_xboole_0(A_205,C_207)),k4_xboole_0(A_205,k4_xboole_0(B_206,C_207))) = k3_xboole_0(k4_xboole_0(A_205,B_206),k3_xboole_0(A_205,C_207)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1857,c_20])).

tff(c_6006,plain,(
    k5_xboole_0(k5_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_3')),k1_xboole_0) = k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_815,c_5856])).

tff(c_6086,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2011,c_735,c_904,c_759,c_904,c_6006])).

tff(c_6172,plain,(
    k5_xboole_0('#skF_1',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6086,c_2])).

tff(c_6199,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_759,c_6172])).

tff(c_18,plain,(
    ! [A_17,B_18] : r1_xboole_0(k4_xboole_0(A_17,B_18),B_18) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6280,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6199,c_18])).

tff(c_6311,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_633,c_6280])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:09:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.68/1.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.68/1.96  
% 4.68/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.68/1.96  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.68/1.96  
% 4.68/1.96  %Foreground sorts:
% 4.68/1.96  
% 4.68/1.96  
% 4.68/1.96  %Background operators:
% 4.68/1.96  
% 4.68/1.96  
% 4.68/1.96  %Foreground operators:
% 4.68/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.68/1.96  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.68/1.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.68/1.96  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.68/1.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.68/1.96  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.68/1.96  tff('#skF_2', type, '#skF_2': $i).
% 4.68/1.96  tff('#skF_3', type, '#skF_3': $i).
% 4.68/1.96  tff('#skF_1', type, '#skF_1': $i).
% 4.68/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.68/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.68/1.96  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.68/1.96  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.68/1.96  
% 4.68/1.97  tff(f_58, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 4.68/1.97  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.68/1.97  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.68/1.97  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.68/1.97  tff(f_39, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 4.68/1.97  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.68/1.97  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.68/1.97  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.68/1.97  tff(f_47, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 4.68/1.97  tff(f_51, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 4.68/1.97  tff(f_49, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.68/1.97  tff(c_22, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.68/1.97  tff(c_51, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_22])).
% 4.68/1.97  tff(c_24, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.68/1.97  tff(c_10, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.68/1.97  tff(c_306, plain, (![A_45, C_46, B_47]: (r1_tarski(A_45, C_46) | ~r1_tarski(B_47, C_46) | ~r1_tarski(A_45, B_47))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.68/1.97  tff(c_579, plain, (![A_59, A_60, B_61]: (r1_tarski(A_59, A_60) | ~r1_tarski(A_59, k4_xboole_0(A_60, B_61)))), inference(resolution, [status(thm)], [c_10, c_306])).
% 4.68/1.97  tff(c_615, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_579])).
% 4.68/1.97  tff(c_632, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_615])).
% 4.68/1.97  tff(c_633, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_22])).
% 4.68/1.97  tff(c_12, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.68/1.97  tff(c_8, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.68/1.97  tff(c_737, plain, (![A_70, B_71]: (k5_xboole_0(A_70, k3_xboole_0(A_70, B_71))=k4_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.68/1.97  tff(c_755, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=k4_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_737])).
% 4.68/1.97  tff(c_759, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_755])).
% 4.68/1.97  tff(c_46, plain, (![A_26, B_27]: (r1_tarski(k4_xboole_0(A_26, B_27), A_26))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.68/1.97  tff(c_49, plain, (![A_11]: (r1_tarski(A_11, A_11))), inference(superposition, [status(thm), theory('equality')], [c_12, c_46])).
% 4.68/1.97  tff(c_635, plain, (![A_62, B_63]: (k3_xboole_0(A_62, B_63)=A_62 | ~r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.68/1.97  tff(c_649, plain, (![A_11]: (k3_xboole_0(A_11, A_11)=A_11)), inference(resolution, [status(thm)], [c_49, c_635])).
% 4.68/1.97  tff(c_679, plain, (![A_65, B_66]: (k4_xboole_0(A_65, k4_xboole_0(A_65, B_66))=k3_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.68/1.97  tff(c_700, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k3_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_679])).
% 4.68/1.97  tff(c_704, plain, (![A_67]: (k4_xboole_0(A_67, A_67)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_700])).
% 4.68/1.97  tff(c_731, plain, (![A_68]: (r1_tarski(k1_xboole_0, A_68))), inference(superposition, [status(thm), theory('equality')], [c_704, c_10])).
% 4.68/1.97  tff(c_6, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.68/1.97  tff(c_786, plain, (![A_74]: (k3_xboole_0(k1_xboole_0, A_74)=k1_xboole_0)), inference(resolution, [status(thm)], [c_731, c_6])).
% 4.68/1.97  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.68/1.97  tff(c_791, plain, (![A_74]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_74))), inference(superposition, [status(thm), theory('equality')], [c_786, c_2])).
% 4.68/1.97  tff(c_809, plain, (![A_74]: (k4_xboole_0(k1_xboole_0, A_74)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_759, c_791])).
% 4.68/1.97  tff(c_1857, plain, (![A_119, B_120, C_121]: (k2_xboole_0(k4_xboole_0(A_119, B_120), k3_xboole_0(A_119, C_121))=k4_xboole_0(A_119, k4_xboole_0(B_120, C_121)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.68/1.97  tff(c_1914, plain, (![A_11, C_121]: (k4_xboole_0(A_11, k4_xboole_0(k1_xboole_0, C_121))=k2_xboole_0(A_11, k3_xboole_0(A_11, C_121)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1857])).
% 4.68/1.97  tff(c_1939, plain, (![A_122, C_123]: (k2_xboole_0(A_122, k3_xboole_0(A_122, C_123))=A_122)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_809, c_1914])).
% 4.68/1.97  tff(c_1963, plain, (![A_11]: (k2_xboole_0(A_11, A_11)=A_11)), inference(superposition, [status(thm), theory('equality')], [c_649, c_1939])).
% 4.68/1.97  tff(c_703, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_700])).
% 4.68/1.97  tff(c_746, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k4_xboole_0(A_11, A_11))), inference(superposition, [status(thm), theory('equality')], [c_649, c_737])).
% 4.68/1.97  tff(c_758, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_703, c_746])).
% 4.68/1.97  tff(c_1426, plain, (![A_103, B_104]: (k5_xboole_0(k5_xboole_0(A_103, B_104), k2_xboole_0(A_103, B_104))=k3_xboole_0(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.68/1.97  tff(c_1441, plain, (![A_11]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_11, A_11))=k3_xboole_0(A_11, A_11))), inference(superposition, [status(thm), theory('equality')], [c_758, c_1426])).
% 4.68/1.97  tff(c_1450, plain, (![A_11]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_11, A_11))=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_649, c_1441])).
% 4.68/1.97  tff(c_2011, plain, (![A_11]: (k5_xboole_0(k1_xboole_0, A_11)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_1963, c_1450])).
% 4.68/1.97  tff(c_735, plain, (![A_68]: (k3_xboole_0(k1_xboole_0, A_68)=k1_xboole_0)), inference(resolution, [status(thm)], [c_731, c_6])).
% 4.68/1.97  tff(c_634, plain, (r1_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_22])).
% 4.68/1.97  tff(c_648, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_634, c_635])).
% 4.68/1.97  tff(c_752, plain, (k5_xboole_0('#skF_1', '#skF_1')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_648, c_737])).
% 4.68/1.97  tff(c_904, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_758, c_752])).
% 4.68/1.97  tff(c_650, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_24, c_635])).
% 4.68/1.97  tff(c_749, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k5_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_650, c_737])).
% 4.68/1.97  tff(c_815, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_758, c_749])).
% 4.68/1.97  tff(c_20, plain, (![A_19, B_20]: (k5_xboole_0(k5_xboole_0(A_19, B_20), k2_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.68/1.97  tff(c_5856, plain, (![A_205, B_206, C_207]: (k5_xboole_0(k5_xboole_0(k4_xboole_0(A_205, B_206), k3_xboole_0(A_205, C_207)), k4_xboole_0(A_205, k4_xboole_0(B_206, C_207)))=k3_xboole_0(k4_xboole_0(A_205, B_206), k3_xboole_0(A_205, C_207)))), inference(superposition, [status(thm), theory('equality')], [c_1857, c_20])).
% 4.68/1.97  tff(c_6006, plain, (k5_xboole_0(k5_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_3')), k1_xboole_0)=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_815, c_5856])).
% 4.68/1.97  tff(c_6086, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2011, c_735, c_904, c_759, c_904, c_6006])).
% 4.68/1.97  tff(c_6172, plain, (k5_xboole_0('#skF_1', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6086, c_2])).
% 4.68/1.97  tff(c_6199, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_759, c_6172])).
% 4.68/1.97  tff(c_18, plain, (![A_17, B_18]: (r1_xboole_0(k4_xboole_0(A_17, B_18), B_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.68/1.97  tff(c_6280, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6199, c_18])).
% 4.68/1.97  tff(c_6311, plain, $false, inference(negUnitSimplification, [status(thm)], [c_633, c_6280])).
% 4.68/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.68/1.97  
% 4.68/1.97  Inference rules
% 4.68/1.97  ----------------------
% 4.68/1.97  #Ref     : 0
% 4.68/1.97  #Sup     : 1569
% 4.68/1.97  #Fact    : 0
% 4.68/1.97  #Define  : 0
% 4.68/1.97  #Split   : 2
% 4.68/1.97  #Chain   : 0
% 4.68/1.97  #Close   : 0
% 4.68/1.97  
% 4.68/1.97  Ordering : KBO
% 4.68/1.97  
% 4.68/1.97  Simplification rules
% 4.68/1.97  ----------------------
% 4.68/1.97  #Subsume      : 59
% 4.68/1.97  #Demod        : 1690
% 4.68/1.97  #Tautology    : 1056
% 4.68/1.97  #SimpNegUnit  : 2
% 4.68/1.97  #BackRed      : 5
% 4.68/1.97  
% 4.68/1.97  #Partial instantiations: 0
% 4.68/1.97  #Strategies tried      : 1
% 4.68/1.97  
% 4.68/1.97  Timing (in seconds)
% 4.68/1.97  ----------------------
% 4.68/1.98  Preprocessing        : 0.27
% 4.68/1.98  Parsing              : 0.16
% 4.68/1.98  CNF conversion       : 0.02
% 4.68/1.98  Main loop            : 0.93
% 4.68/1.98  Inferencing          : 0.32
% 4.68/1.98  Reduction            : 0.39
% 4.68/1.98  Demodulation         : 0.31
% 4.68/1.98  BG Simplification    : 0.03
% 4.68/1.98  Subsumption          : 0.13
% 4.68/1.98  Abstraction          : 0.05
% 4.68/1.98  MUC search           : 0.00
% 4.68/1.98  Cooper               : 0.00
% 4.68/1.98  Total                : 1.23
% 4.68/1.98  Index Insertion      : 0.00
% 4.68/1.98  Index Deletion       : 0.00
% 4.68/1.98  Index Matching       : 0.00
% 4.68/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
