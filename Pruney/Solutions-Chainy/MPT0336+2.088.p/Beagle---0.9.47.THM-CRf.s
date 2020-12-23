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
% DateTime   : Thu Dec  3 09:55:12 EST 2020

% Result     : Theorem 9.94s
% Output     : CNFRefutation 10.08s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 155 expanded)
%              Number of leaves         :   28 (  63 expanded)
%              Depth                    :   14
%              Number of atoms          :  124 ( 289 expanded)
%              Number of equality atoms :   27 (  51 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
        & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).

tff(c_42,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_58,plain,(
    ! [B_33,A_34] :
      ( r1_xboole_0(B_33,A_34)
      | ~ r1_xboole_0(A_34,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_58])).

tff(c_1100,plain,(
    ! [A_115,C_116,B_117] :
      ( ~ r1_xboole_0(A_115,C_116)
      | ~ r1_xboole_0(A_115,B_117)
      | r1_xboole_0(A_115,k2_xboole_0(B_117,C_116)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3468,plain,(
    ! [B_225,C_226,A_227] :
      ( r1_xboole_0(k2_xboole_0(B_225,C_226),A_227)
      | ~ r1_xboole_0(A_227,C_226)
      | ~ r1_xboole_0(A_227,B_225) ) ),
    inference(resolution,[status(thm)],[c_1100,c_4])).

tff(c_40,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3486,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_3468,c_40])).

tff(c_3494,plain,(
    ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_3486])).

tff(c_26,plain,(
    ! [A_21,B_22] : r1_xboole_0(k4_xboole_0(A_21,B_22),B_22) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_63,plain,(
    ! [B_22,A_21] : r1_xboole_0(B_22,k4_xboole_0(A_21,B_22)) ),
    inference(resolution,[status(thm)],[c_26,c_58])).

tff(c_28,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(A_23,B_24) = A_23
      | ~ r1_xboole_0(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1117,plain,(
    ! [A_115,B_117,C_116] :
      ( k4_xboole_0(A_115,k2_xboole_0(B_117,C_116)) = A_115
      | ~ r1_xboole_0(A_115,C_116)
      | ~ r1_xboole_0(A_115,B_117) ) ),
    inference(resolution,[status(thm)],[c_1100,c_28])).

tff(c_273,plain,(
    ! [A_65,B_66] :
      ( k4_xboole_0(A_65,k1_tarski(B_66)) = A_65
      | r2_hidden(B_66,A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_321,plain,(
    ! [B_72,A_73] :
      ( r1_xboole_0(k1_tarski(B_72),A_73)
      | r2_hidden(B_72,A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_63])).

tff(c_22,plain,(
    ! [A_15,B_16,C_17] :
      ( r1_xboole_0(A_15,B_16)
      | ~ r1_xboole_0(A_15,k2_xboole_0(B_16,C_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_336,plain,(
    ! [B_72,B_16,C_17] :
      ( r1_xboole_0(k1_tarski(B_72),B_16)
      | r2_hidden(B_72,k2_xboole_0(B_16,C_17)) ) ),
    inference(resolution,[status(thm)],[c_321,c_22])).

tff(c_44,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_107,plain,(
    ! [A_39,B_40] :
      ( r1_xboole_0(A_39,B_40)
      | k4_xboole_0(A_39,B_40) != A_39 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_113,plain,(
    ! [B_40,A_39] :
      ( r1_xboole_0(B_40,A_39)
      | k4_xboole_0(A_39,B_40) != A_39 ) ),
    inference(resolution,[status(thm)],[c_107,c_4])).

tff(c_969,plain,(
    ! [A_110,B_111,C_112] :
      ( ~ r1_xboole_0(A_110,B_111)
      | ~ r2_hidden(C_112,B_111)
      | ~ r2_hidden(C_112,A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12167,plain,(
    ! [C_501,A_502,B_503] :
      ( ~ r2_hidden(C_501,A_502)
      | ~ r2_hidden(C_501,B_503)
      | k4_xboole_0(A_502,B_503) != A_502 ) ),
    inference(resolution,[status(thm)],[c_113,c_969])).

tff(c_12195,plain,(
    ! [B_504] :
      ( ~ r2_hidden('#skF_5',B_504)
      | k4_xboole_0('#skF_4',B_504) != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_44,c_12167])).

tff(c_13332,plain,(
    ! [B_539,C_540] :
      ( k4_xboole_0('#skF_4',k2_xboole_0(B_539,C_540)) != '#skF_4'
      | r1_xboole_0(k1_tarski('#skF_5'),B_539) ) ),
    inference(resolution,[status(thm)],[c_336,c_12195])).

tff(c_13344,plain,(
    ! [B_117,C_116] :
      ( r1_xboole_0(k1_tarski('#skF_5'),B_117)
      | ~ r1_xboole_0('#skF_4',C_116)
      | ~ r1_xboole_0('#skF_4',B_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1117,c_13332])).

tff(c_13878,plain,(
    ! [C_116] : ~ r1_xboole_0('#skF_4',C_116) ),
    inference(splitLeft,[status(thm)],[c_13344])).

tff(c_13883,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13878,c_42])).

tff(c_13885,plain,(
    ! [B_553] :
      ( r1_xboole_0(k1_tarski('#skF_5'),B_553)
      | ~ r1_xboole_0('#skF_4',B_553) ) ),
    inference(splitRight,[status(thm)],[c_13344])).

tff(c_13944,plain,(
    ! [B_553] :
      ( r1_xboole_0(B_553,k1_tarski('#skF_5'))
      | ~ r1_xboole_0('#skF_4',B_553) ) ),
    inference(resolution,[status(thm)],[c_13885,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_46,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_47,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_46])).

tff(c_115,plain,(
    ! [A_41,B_42] :
      ( k4_xboole_0(A_41,B_42) = A_41
      | ~ r1_xboole_0(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_132,plain,(
    ! [B_22,A_21] : k4_xboole_0(B_22,k4_xboole_0(A_21,B_22)) = B_22 ),
    inference(resolution,[status(thm)],[c_63,c_115])).

tff(c_528,plain,(
    ! [A_80,C_81,B_82] :
      ( r1_xboole_0(A_80,C_81)
      | ~ r1_tarski(A_80,k4_xboole_0(B_82,C_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1727,plain,(
    ! [A_160,A_161,B_162] :
      ( r1_xboole_0(A_160,k4_xboole_0(A_161,B_162))
      | ~ r1_tarski(A_160,B_162) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_528])).

tff(c_10773,plain,(
    ! [A_465,A_466,B_467] :
      ( k4_xboole_0(A_465,k4_xboole_0(A_466,B_467)) = A_465
      | ~ r1_tarski(A_465,B_467) ) ),
    inference(resolution,[status(thm)],[c_1727,c_28])).

tff(c_16,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_11024,plain,(
    ! [A_468,B_469] :
      ( k3_xboole_0(A_468,B_469) = A_468
      | ~ r1_tarski(A_468,B_469) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10773,c_16])).

tff(c_11036,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_47,c_11024])).

tff(c_663,plain,(
    ! [A_89,B_90,C_91] :
      ( ~ r1_xboole_0(A_89,B_90)
      | r1_xboole_0(A_89,k3_xboole_0(B_90,C_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1415,plain,(
    ! [A_143,B_144,C_145] :
      ( k4_xboole_0(A_143,k3_xboole_0(B_144,C_145)) = A_143
      | ~ r1_xboole_0(A_143,B_144) ) ),
    inference(resolution,[status(thm)],[c_663,c_28])).

tff(c_1492,plain,(
    ! [A_143,A_1,B_2] :
      ( k4_xboole_0(A_143,k3_xboole_0(A_1,B_2)) = A_143
      | ~ r1_xboole_0(A_143,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1415])).

tff(c_15347,plain,(
    ! [A_579] :
      ( k4_xboole_0(A_579,k3_xboole_0('#skF_3','#skF_2')) = A_579
      | ~ r1_xboole_0(A_579,k1_tarski('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11036,c_1492])).

tff(c_15533,plain,(
    ! [B_580] :
      ( k4_xboole_0(B_580,k3_xboole_0('#skF_3','#skF_2')) = B_580
      | ~ r1_xboole_0('#skF_4',B_580) ) ),
    inference(resolution,[status(thm)],[c_13944,c_15347])).

tff(c_339,plain,(
    ! [A_74,B_75] : k4_xboole_0(A_74,k4_xboole_0(A_74,B_75)) = k3_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_342,plain,(
    ! [A_74,B_75] : k4_xboole_0(A_74,k3_xboole_0(A_74,B_75)) = k3_xboole_0(A_74,k4_xboole_0(A_74,B_75)) ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_16])).

tff(c_15620,plain,
    ( k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_2')) = '#skF_3'
    | ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_15533,c_342])).

tff(c_15729,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_15620])).

tff(c_1133,plain,(
    ! [B_120,C_121,A_122] :
      ( r1_xboole_0(k3_xboole_0(B_120,C_121),A_122)
      | ~ r1_xboole_0(A_122,B_120) ) ),
    inference(resolution,[status(thm)],[c_663,c_4])).

tff(c_1154,plain,(
    ! [B_2,A_1,A_122] :
      ( r1_xboole_0(k3_xboole_0(B_2,A_1),A_122)
      | ~ r1_xboole_0(A_122,A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1133])).

tff(c_17657,plain,(
    ! [A_600] :
      ( r1_xboole_0('#skF_3',A_600)
      | ~ r1_xboole_0(A_600,k4_xboole_0('#skF_3','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15729,c_1154])).

tff(c_17807,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_63,c_17657])).

tff(c_17856,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3494,c_17807])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:58:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.94/3.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.08/3.70  
% 10.08/3.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.08/3.70  %$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 10.08/3.70  
% 10.08/3.70  %Foreground sorts:
% 10.08/3.70  
% 10.08/3.70  
% 10.08/3.70  %Background operators:
% 10.08/3.70  
% 10.08/3.70  
% 10.08/3.70  %Foreground operators:
% 10.08/3.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.08/3.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.08/3.70  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.08/3.70  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.08/3.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.08/3.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.08/3.70  tff('#skF_5', type, '#skF_5': $i).
% 10.08/3.70  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.08/3.70  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.08/3.70  tff('#skF_2', type, '#skF_2': $i).
% 10.08/3.70  tff('#skF_3', type, '#skF_3': $i).
% 10.08/3.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.08/3.70  tff('#skF_4', type, '#skF_4': $i).
% 10.08/3.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.08/3.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.08/3.70  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.08/3.70  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.08/3.70  
% 10.08/3.71  tff(f_103, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 10.08/3.71  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 10.08/3.71  tff(f_73, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 10.08/3.71  tff(f_81, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 10.08/3.71  tff(f_85, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 10.08/3.71  tff(f_94, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 10.08/3.71  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 10.08/3.71  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.08/3.71  tff(f_55, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 10.08/3.71  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.08/3.71  tff(f_79, axiom, (![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_xboole_1)).
% 10.08/3.71  tff(c_42, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.08/3.71  tff(c_58, plain, (![B_33, A_34]: (r1_xboole_0(B_33, A_34) | ~r1_xboole_0(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.08/3.71  tff(c_64, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_58])).
% 10.08/3.71  tff(c_1100, plain, (![A_115, C_116, B_117]: (~r1_xboole_0(A_115, C_116) | ~r1_xboole_0(A_115, B_117) | r1_xboole_0(A_115, k2_xboole_0(B_117, C_116)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.08/3.71  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.08/3.71  tff(c_3468, plain, (![B_225, C_226, A_227]: (r1_xboole_0(k2_xboole_0(B_225, C_226), A_227) | ~r1_xboole_0(A_227, C_226) | ~r1_xboole_0(A_227, B_225))), inference(resolution, [status(thm)], [c_1100, c_4])).
% 10.08/3.71  tff(c_40, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.08/3.71  tff(c_3486, plain, (~r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_3468, c_40])).
% 10.08/3.71  tff(c_3494, plain, (~r1_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_3486])).
% 10.08/3.71  tff(c_26, plain, (![A_21, B_22]: (r1_xboole_0(k4_xboole_0(A_21, B_22), B_22))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.08/3.71  tff(c_63, plain, (![B_22, A_21]: (r1_xboole_0(B_22, k4_xboole_0(A_21, B_22)))), inference(resolution, [status(thm)], [c_26, c_58])).
% 10.08/3.71  tff(c_28, plain, (![A_23, B_24]: (k4_xboole_0(A_23, B_24)=A_23 | ~r1_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.08/3.71  tff(c_1117, plain, (![A_115, B_117, C_116]: (k4_xboole_0(A_115, k2_xboole_0(B_117, C_116))=A_115 | ~r1_xboole_0(A_115, C_116) | ~r1_xboole_0(A_115, B_117))), inference(resolution, [status(thm)], [c_1100, c_28])).
% 10.08/3.71  tff(c_273, plain, (![A_65, B_66]: (k4_xboole_0(A_65, k1_tarski(B_66))=A_65 | r2_hidden(B_66, A_65))), inference(cnfTransformation, [status(thm)], [f_94])).
% 10.08/3.71  tff(c_321, plain, (![B_72, A_73]: (r1_xboole_0(k1_tarski(B_72), A_73) | r2_hidden(B_72, A_73))), inference(superposition, [status(thm), theory('equality')], [c_273, c_63])).
% 10.08/3.71  tff(c_22, plain, (![A_15, B_16, C_17]: (r1_xboole_0(A_15, B_16) | ~r1_xboole_0(A_15, k2_xboole_0(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.08/3.71  tff(c_336, plain, (![B_72, B_16, C_17]: (r1_xboole_0(k1_tarski(B_72), B_16) | r2_hidden(B_72, k2_xboole_0(B_16, C_17)))), inference(resolution, [status(thm)], [c_321, c_22])).
% 10.08/3.71  tff(c_44, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.08/3.71  tff(c_107, plain, (![A_39, B_40]: (r1_xboole_0(A_39, B_40) | k4_xboole_0(A_39, B_40)!=A_39)), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.08/3.71  tff(c_113, plain, (![B_40, A_39]: (r1_xboole_0(B_40, A_39) | k4_xboole_0(A_39, B_40)!=A_39)), inference(resolution, [status(thm)], [c_107, c_4])).
% 10.08/3.71  tff(c_969, plain, (![A_110, B_111, C_112]: (~r1_xboole_0(A_110, B_111) | ~r2_hidden(C_112, B_111) | ~r2_hidden(C_112, A_110))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.08/3.71  tff(c_12167, plain, (![C_501, A_502, B_503]: (~r2_hidden(C_501, A_502) | ~r2_hidden(C_501, B_503) | k4_xboole_0(A_502, B_503)!=A_502)), inference(resolution, [status(thm)], [c_113, c_969])).
% 10.08/3.71  tff(c_12195, plain, (![B_504]: (~r2_hidden('#skF_5', B_504) | k4_xboole_0('#skF_4', B_504)!='#skF_4')), inference(resolution, [status(thm)], [c_44, c_12167])).
% 10.08/3.71  tff(c_13332, plain, (![B_539, C_540]: (k4_xboole_0('#skF_4', k2_xboole_0(B_539, C_540))!='#skF_4' | r1_xboole_0(k1_tarski('#skF_5'), B_539))), inference(resolution, [status(thm)], [c_336, c_12195])).
% 10.08/3.71  tff(c_13344, plain, (![B_117, C_116]: (r1_xboole_0(k1_tarski('#skF_5'), B_117) | ~r1_xboole_0('#skF_4', C_116) | ~r1_xboole_0('#skF_4', B_117))), inference(superposition, [status(thm), theory('equality')], [c_1117, c_13332])).
% 10.08/3.71  tff(c_13878, plain, (![C_116]: (~r1_xboole_0('#skF_4', C_116))), inference(splitLeft, [status(thm)], [c_13344])).
% 10.08/3.71  tff(c_13883, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13878, c_42])).
% 10.08/3.71  tff(c_13885, plain, (![B_553]: (r1_xboole_0(k1_tarski('#skF_5'), B_553) | ~r1_xboole_0('#skF_4', B_553))), inference(splitRight, [status(thm)], [c_13344])).
% 10.08/3.71  tff(c_13944, plain, (![B_553]: (r1_xboole_0(B_553, k1_tarski('#skF_5')) | ~r1_xboole_0('#skF_4', B_553))), inference(resolution, [status(thm)], [c_13885, c_4])).
% 10.08/3.71  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.08/3.71  tff(c_46, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.08/3.71  tff(c_47, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_46])).
% 10.08/3.71  tff(c_115, plain, (![A_41, B_42]: (k4_xboole_0(A_41, B_42)=A_41 | ~r1_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.08/3.71  tff(c_132, plain, (![B_22, A_21]: (k4_xboole_0(B_22, k4_xboole_0(A_21, B_22))=B_22)), inference(resolution, [status(thm)], [c_63, c_115])).
% 10.08/3.71  tff(c_528, plain, (![A_80, C_81, B_82]: (r1_xboole_0(A_80, C_81) | ~r1_tarski(A_80, k4_xboole_0(B_82, C_81)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.08/3.71  tff(c_1727, plain, (![A_160, A_161, B_162]: (r1_xboole_0(A_160, k4_xboole_0(A_161, B_162)) | ~r1_tarski(A_160, B_162))), inference(superposition, [status(thm), theory('equality')], [c_132, c_528])).
% 10.08/3.71  tff(c_10773, plain, (![A_465, A_466, B_467]: (k4_xboole_0(A_465, k4_xboole_0(A_466, B_467))=A_465 | ~r1_tarski(A_465, B_467))), inference(resolution, [status(thm)], [c_1727, c_28])).
% 10.08/3.71  tff(c_16, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.08/3.71  tff(c_11024, plain, (![A_468, B_469]: (k3_xboole_0(A_468, B_469)=A_468 | ~r1_tarski(A_468, B_469))), inference(superposition, [status(thm), theory('equality')], [c_10773, c_16])).
% 10.08/3.71  tff(c_11036, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))=k3_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_47, c_11024])).
% 10.08/3.71  tff(c_663, plain, (![A_89, B_90, C_91]: (~r1_xboole_0(A_89, B_90) | r1_xboole_0(A_89, k3_xboole_0(B_90, C_91)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.08/3.71  tff(c_1415, plain, (![A_143, B_144, C_145]: (k4_xboole_0(A_143, k3_xboole_0(B_144, C_145))=A_143 | ~r1_xboole_0(A_143, B_144))), inference(resolution, [status(thm)], [c_663, c_28])).
% 10.08/3.71  tff(c_1492, plain, (![A_143, A_1, B_2]: (k4_xboole_0(A_143, k3_xboole_0(A_1, B_2))=A_143 | ~r1_xboole_0(A_143, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1415])).
% 10.08/3.71  tff(c_15347, plain, (![A_579]: (k4_xboole_0(A_579, k3_xboole_0('#skF_3', '#skF_2'))=A_579 | ~r1_xboole_0(A_579, k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_11036, c_1492])).
% 10.08/3.71  tff(c_15533, plain, (![B_580]: (k4_xboole_0(B_580, k3_xboole_0('#skF_3', '#skF_2'))=B_580 | ~r1_xboole_0('#skF_4', B_580))), inference(resolution, [status(thm)], [c_13944, c_15347])).
% 10.08/3.71  tff(c_339, plain, (![A_74, B_75]: (k4_xboole_0(A_74, k4_xboole_0(A_74, B_75))=k3_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.08/3.71  tff(c_342, plain, (![A_74, B_75]: (k4_xboole_0(A_74, k3_xboole_0(A_74, B_75))=k3_xboole_0(A_74, k4_xboole_0(A_74, B_75)))), inference(superposition, [status(thm), theory('equality')], [c_339, c_16])).
% 10.08/3.71  tff(c_15620, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_2'))='#skF_3' | ~r1_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_15533, c_342])).
% 10.08/3.71  tff(c_15729, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_15620])).
% 10.08/3.71  tff(c_1133, plain, (![B_120, C_121, A_122]: (r1_xboole_0(k3_xboole_0(B_120, C_121), A_122) | ~r1_xboole_0(A_122, B_120))), inference(resolution, [status(thm)], [c_663, c_4])).
% 10.08/3.71  tff(c_1154, plain, (![B_2, A_1, A_122]: (r1_xboole_0(k3_xboole_0(B_2, A_1), A_122) | ~r1_xboole_0(A_122, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1133])).
% 10.08/3.71  tff(c_17657, plain, (![A_600]: (r1_xboole_0('#skF_3', A_600) | ~r1_xboole_0(A_600, k4_xboole_0('#skF_3', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_15729, c_1154])).
% 10.08/3.71  tff(c_17807, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_63, c_17657])).
% 10.08/3.71  tff(c_17856, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3494, c_17807])).
% 10.08/3.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.08/3.71  
% 10.08/3.71  Inference rules
% 10.08/3.71  ----------------------
% 10.08/3.71  #Ref     : 1
% 10.08/3.71  #Sup     : 4442
% 10.08/3.71  #Fact    : 0
% 10.08/3.71  #Define  : 0
% 10.08/3.71  #Split   : 7
% 10.08/3.71  #Chain   : 0
% 10.08/3.71  #Close   : 0
% 10.08/3.71  
% 10.08/3.71  Ordering : KBO
% 10.08/3.71  
% 10.08/3.71  Simplification rules
% 10.08/3.71  ----------------------
% 10.08/3.72  #Subsume      : 825
% 10.08/3.72  #Demod        : 1919
% 10.08/3.72  #Tautology    : 1664
% 10.08/3.72  #SimpNegUnit  : 46
% 10.08/3.72  #BackRed      : 15
% 10.08/3.72  
% 10.08/3.72  #Partial instantiations: 0
% 10.08/3.72  #Strategies tried      : 1
% 10.08/3.72  
% 10.08/3.72  Timing (in seconds)
% 10.08/3.72  ----------------------
% 10.08/3.72  Preprocessing        : 0.39
% 10.08/3.72  Parsing              : 0.20
% 10.08/3.72  CNF conversion       : 0.02
% 10.08/3.72  Main loop            : 2.51
% 10.08/3.72  Inferencing          : 0.59
% 10.08/3.72  Reduction            : 1.04
% 10.08/3.72  Demodulation         : 0.81
% 10.08/3.72  BG Simplification    : 0.07
% 10.08/3.72  Subsumption          : 0.63
% 10.08/3.72  Abstraction          : 0.09
% 10.08/3.72  MUC search           : 0.00
% 10.08/3.72  Cooper               : 0.00
% 10.08/3.72  Total                : 2.93
% 10.08/3.72  Index Insertion      : 0.00
% 10.08/3.72  Index Deletion       : 0.00
% 10.08/3.72  Index Matching       : 0.00
% 10.08/3.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
