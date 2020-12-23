%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:38 EST 2020

% Result     : Theorem 12.65s
% Output     : CNFRefutation 12.79s
% Verified   : 
% Statistics : Number of formulae       :  190 ( 443 expanded)
%              Number of leaves         :   33 ( 151 expanded)
%              Depth                    :   15
%              Number of atoms          :  237 ( 813 expanded)
%              Number of equality atoms :   78 ( 191 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_112,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
            & r1_xboole_0(A,B)
            & r1_xboole_0(A,C) )
        & ~ ( ~ ( r1_xboole_0(A,B)
                & r1_xboole_0(A,C) )
            & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_53,axiom,(
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

tff(f_67,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_75,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_95,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_85,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_77,axiom,(
    ! [A,B,C] : r1_tarski(k3_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).

tff(f_79,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_44493,plain,(
    ! [A_992,B_993] :
      ( r1_xboole_0(A_992,B_993)
      | k3_xboole_0(A_992,B_993) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_47306,plain,(
    ! [B_1132,A_1133] :
      ( r1_xboole_0(B_1132,A_1133)
      | k3_xboole_0(A_1133,B_1132) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_44493,c_8])).

tff(c_45564,plain,(
    ! [B_1057,A_1058] :
      ( r1_xboole_0(B_1057,A_1058)
      | k3_xboole_0(A_1058,B_1057) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_44493,c_8])).

tff(c_144,plain,(
    ! [A_55,B_56] :
      ( r1_xboole_0(A_55,B_56)
      | k3_xboole_0(A_55,B_56) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_42797,plain,(
    ! [B_941,A_942] :
      ( r1_xboole_0(B_941,A_942)
      | k3_xboole_0(A_942,B_941) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_144,c_8])).

tff(c_40117,plain,(
    ! [B_847,A_848] :
      ( r1_xboole_0(B_847,A_848)
      | k3_xboole_0(A_848,B_847) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_144,c_8])).

tff(c_29875,plain,(
    ! [B_623,A_624] :
      ( r1_xboole_0(B_623,A_624)
      | k3_xboole_0(A_624,B_623) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_144,c_8])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_44,plain,
    ( r1_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5'))
    | r1_xboole_0('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_197,plain,(
    r1_xboole_0('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_203,plain,(
    k3_xboole_0('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_197,c_2])).

tff(c_403,plain,(
    ! [A_70,B_71] :
      ( r2_hidden('#skF_1'(A_70,B_71),B_71)
      | r1_xboole_0(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_358,plain,(
    ! [A_66,B_67,C_68] :
      ( ~ r1_xboole_0(A_66,B_67)
      | ~ r2_hidden(C_68,k3_xboole_0(A_66,B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_364,plain,(
    ! [C_68] :
      ( ~ r1_xboole_0('#skF_6','#skF_7')
      | ~ r2_hidden(C_68,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_358])).

tff(c_374,plain,(
    ! [C_68] : ~ r2_hidden(C_68,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_364])).

tff(c_414,plain,(
    ! [A_72] : r1_xboole_0(A_72,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_403,c_374])).

tff(c_431,plain,(
    ! [A_74] : k3_xboole_0(A_74,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_414,c_2])).

tff(c_22,plain,(
    ! [A_19,B_20] : k2_xboole_0(A_19,k3_xboole_0(A_19,B_20)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_448,plain,(
    ! [A_74] : k2_xboole_0(A_74,k1_xboole_0) = A_74 ),
    inference(superposition,[status(thm),theory(equality)],[c_431,c_22])).

tff(c_40,plain,
    ( r1_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5'))
    | r1_xboole_0('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_102,plain,(
    r1_xboole_0('#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_108,plain,(
    k3_xboole_0('#skF_6','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_102,c_2])).

tff(c_1606,plain,(
    ! [A_122,B_123,C_124] : k2_xboole_0(k3_xboole_0(A_122,B_123),k3_xboole_0(A_122,C_124)) = k3_xboole_0(A_122,k2_xboole_0(B_123,C_124)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1681,plain,(
    ! [B_123] : k3_xboole_0('#skF_6',k2_xboole_0(B_123,'#skF_8')) = k2_xboole_0(k3_xboole_0('#skF_6',B_123),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_1606])).

tff(c_1706,plain,(
    ! [B_123] : k3_xboole_0('#skF_6',k2_xboole_0(B_123,'#skF_8')) = k3_xboole_0('#skF_6',B_123) ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_1681])).

tff(c_48,plain,
    ( r1_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5'))
    | ~ r1_xboole_0('#skF_6',k2_xboole_0('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_455,plain,(
    ~ r1_xboole_0('#skF_6',k2_xboole_0('#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_619,plain,(
    k3_xboole_0('#skF_6',k2_xboole_0('#skF_7','#skF_8')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_455])).

tff(c_24491,plain,(
    k3_xboole_0('#skF_6','#skF_7') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1706,c_619])).

tff(c_24494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_24491])).

tff(c_24496,plain,(
    r1_xboole_0('#skF_6',k2_xboole_0('#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_50,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_6',k2_xboole_0('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_24681,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24496,c_50])).

tff(c_24682,plain,(
    ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_24681])).

tff(c_24686,plain,(
    k3_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_24682])).

tff(c_420,plain,(
    ! [A_72] : k3_xboole_0(A_72,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_414,c_2])).

tff(c_24495,plain,(
    r1_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_24662,plain,(
    k3_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24495,c_2])).

tff(c_25732,plain,(
    ! [A_504,B_505,C_506] : k2_xboole_0(k3_xboole_0(A_504,B_505),k3_xboole_0(A_504,C_506)) = k3_xboole_0(A_504,k2_xboole_0(B_505,C_506)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_38,plain,(
    ! [A_40,B_41] : r1_tarski(A_40,k2_xboole_0(A_40,B_41)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_28306,plain,(
    ! [A_572,B_573,C_574] : r1_tarski(k3_xboole_0(A_572,B_573),k3_xboole_0(A_572,k2_xboole_0(B_573,C_574))) ),
    inference(superposition,[status(thm),theory(equality)],[c_25732,c_38])).

tff(c_28382,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24662,c_28306])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( k2_xboole_0(A_17,B_18) = B_18
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_28453,plain,(
    k2_xboole_0(k3_xboole_0('#skF_3','#skF_4'),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28382,c_20])).

tff(c_32,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k2_xboole_0(A_33,B_34)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_249,plain,(
    ! [A_62,B_63] : k2_xboole_0(k3_xboole_0(A_62,B_63),k4_xboole_0(A_62,B_63)) = A_62 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_27335,plain,(
    ! [A_543,B_544] : k2_xboole_0(k3_xboole_0(A_543,k2_xboole_0(A_543,B_544)),k1_xboole_0) = A_543 ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_249])).

tff(c_27389,plain,(
    ! [A_543,B_544] : k3_xboole_0(A_543,k2_xboole_0(A_543,B_544)) = A_543 ),
    inference(superposition,[status(thm),theory(equality)],[c_448,c_27335])).

tff(c_28472,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_4'),k1_xboole_0) = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_28453,c_27389])).

tff(c_28495,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_28472])).

tff(c_28497,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24686,c_28495])).

tff(c_28498,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_24681])).

tff(c_29890,plain,(
    k3_xboole_0('#skF_5','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_29875,c_28498])).

tff(c_6,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_174,plain,(
    ! [A_59,B_60,C_61] : r1_tarski(k3_xboole_0(A_59,B_60),k2_xboole_0(A_59,C_61)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_285,plain,(
    ! [A_64,B_65] : r1_tarski(k3_xboole_0(A_64,B_65),A_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_174])).

tff(c_301,plain,(
    ! [A_64,B_65] : k2_xboole_0(k3_xboole_0(A_64,B_65),A_64) = A_64 ),
    inference(resolution,[status(thm)],[c_285,c_20])).

tff(c_67,plain,(
    ! [A_48,B_49] : k4_xboole_0(A_48,k2_xboole_0(A_48,B_49)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_74,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_67])).

tff(c_28769,plain,(
    ! [A_585] : k2_xboole_0(k3_xboole_0(A_585,A_585),k1_xboole_0) = A_585 ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_249])).

tff(c_28775,plain,(
    ! [A_585] : k3_xboole_0(A_585,A_585) = A_585 ),
    inference(superposition,[status(thm),theory(equality)],[c_28769,c_448])).

tff(c_29525,plain,(
    ! [A_614,B_615,C_616] : k2_xboole_0(k3_xboole_0(A_614,B_615),k3_xboole_0(A_614,C_616)) = k3_xboole_0(A_614,k2_xboole_0(B_615,C_616)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_29564,plain,(
    ! [A_585,B_615] : k3_xboole_0(A_585,k2_xboole_0(B_615,A_585)) = k2_xboole_0(k3_xboole_0(A_585,B_615),A_585) ),
    inference(superposition,[status(thm),theory(equality)],[c_28775,c_29525])).

tff(c_32335,plain,(
    ! [A_685,B_686] : k3_xboole_0(A_685,k2_xboole_0(B_686,A_685)) = A_685 ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_29564])).

tff(c_34,plain,(
    ! [A_35,B_36] : k2_xboole_0(k3_xboole_0(A_35,B_36),k4_xboole_0(A_35,B_36)) = A_35 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_24,plain,(
    ! [A_21,B_22,C_23] : k2_xboole_0(k3_xboole_0(A_21,B_22),k3_xboole_0(A_21,C_23)) = k3_xboole_0(A_21,k2_xboole_0(B_22,C_23)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_28,plain,(
    ! [A_27,B_28,C_29] : r1_tarski(k2_xboole_0(k3_xboole_0(A_27,B_28),k3_xboole_0(A_27,C_29)),k2_xboole_0(B_28,C_29)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_29063,plain,(
    ! [A_596,B_597,C_598] : r1_tarski(k3_xboole_0(A_596,k2_xboole_0(B_597,C_598)),k2_xboole_0(B_597,C_598)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28])).

tff(c_29100,plain,(
    ! [A_596,A_35,B_36] : r1_tarski(k3_xboole_0(A_596,A_35),k2_xboole_0(k3_xboole_0(A_35,B_36),k4_xboole_0(A_35,B_36))) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_29063])).

tff(c_29127,plain,(
    ! [A_596,A_35] : r1_tarski(k3_xboole_0(A_596,A_35),A_35) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_29100])).

tff(c_32411,plain,(
    ! [A_685,B_686] : r1_tarski(A_685,k2_xboole_0(B_686,A_685)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32335,c_29127])).

tff(c_24663,plain,(
    r1_xboole_0(k2_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_24495,c_8])).

tff(c_28805,plain,(
    ! [A_586,C_587,B_588] :
      ( r1_xboole_0(A_586,C_587)
      | ~ r1_xboole_0(B_588,C_587)
      | ~ r1_tarski(A_586,B_588) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_38123,plain,(
    ! [A_767] :
      ( r1_xboole_0(A_767,'#skF_3')
      | ~ r1_tarski(A_767,k2_xboole_0('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_24663,c_28805])).

tff(c_38166,plain,(
    r1_xboole_0('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_32411,c_38123])).

tff(c_38182,plain,(
    k3_xboole_0('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38166,c_2])).

tff(c_38190,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_29890,c_38182])).

tff(c_38192,plain,(
    ~ r1_xboole_0('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_46,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ r1_xboole_0('#skF_3','#skF_4')
    | r1_xboole_0('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_38270,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_38192,c_46])).

tff(c_38271,plain,(
    ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_38270])).

tff(c_40140,plain,(
    k3_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40117,c_38271])).

tff(c_38191,plain,(
    r1_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_38203,plain,(
    r1_xboole_0(k2_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_38191,c_8])).

tff(c_38924,plain,(
    ! [A_801,C_802,B_803] :
      ( r1_xboole_0(A_801,C_802)
      | ~ r1_xboole_0(B_803,C_802)
      | ~ r1_tarski(A_801,B_803) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_40773,plain,(
    ! [A_870] :
      ( r1_xboole_0(A_870,'#skF_3')
      | ~ r1_tarski(A_870,k2_xboole_0('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_38203,c_38924])).

tff(c_40825,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_40773])).

tff(c_40832,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40825,c_2])).

tff(c_40840,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40140,c_40832])).

tff(c_40841,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_38270])).

tff(c_42815,plain,(
    k3_xboole_0('#skF_5','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42797,c_40841])).

tff(c_38204,plain,(
    ! [A_768,B_769] : r1_tarski(k3_xboole_0(A_768,B_769),A_768) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_174])).

tff(c_38214,plain,(
    ! [A_768,B_769] : k2_xboole_0(k3_xboole_0(A_768,B_769),A_768) = A_768 ),
    inference(resolution,[status(thm)],[c_38204,c_20])).

tff(c_41086,plain,(
    ! [A_882,B_883] : k2_xboole_0(k3_xboole_0(A_882,B_883),k4_xboole_0(A_882,B_883)) = A_882 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_41635,plain,(
    ! [A_906] : k2_xboole_0(k3_xboole_0(A_906,A_906),k1_xboole_0) = A_906 ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_41086])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_1'(A_7,B_8),B_8)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_40862,plain,(
    ! [A_871,B_872,C_873] :
      ( ~ r1_xboole_0(A_871,B_872)
      | ~ r2_hidden(C_873,k3_xboole_0(A_871,B_872)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_40872,plain,(
    ! [C_873] :
      ( ~ r1_xboole_0('#skF_6','#skF_8')
      | ~ r2_hidden(C_873,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_40862])).

tff(c_40878,plain,(
    ! [C_874] : ~ r2_hidden(C_874,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_40872])).

tff(c_40884,plain,(
    ! [A_875] : r1_xboole_0(A_875,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_40878])).

tff(c_41006,plain,(
    ! [A_879] : k3_xboole_0(A_879,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40884,c_2])).

tff(c_41020,plain,(
    ! [A_879] : k2_xboole_0(A_879,k1_xboole_0) = A_879 ),
    inference(superposition,[status(thm),theory(equality)],[c_41006,c_22])).

tff(c_41645,plain,(
    ! [A_906] : k3_xboole_0(A_906,A_906) = A_906 ),
    inference(superposition,[status(thm),theory(equality)],[c_41635,c_41020])).

tff(c_42124,plain,(
    ! [A_924,B_925,C_926] : k2_xboole_0(k3_xboole_0(A_924,B_925),k3_xboole_0(A_924,C_926)) = k3_xboole_0(A_924,k2_xboole_0(B_925,C_926)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_42159,plain,(
    ! [A_906,B_925] : k3_xboole_0(A_906,k2_xboole_0(B_925,A_906)) = k2_xboole_0(k3_xboole_0(A_906,B_925),A_906) ),
    inference(superposition,[status(thm),theory(equality)],[c_41645,c_42124])).

tff(c_43695,plain,(
    ! [A_972,B_973] : k3_xboole_0(A_972,k2_xboole_0(B_973,A_972)) = A_972 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38214,c_42159])).

tff(c_41297,plain,(
    ! [A_887,B_888,C_889] : r1_tarski(k3_xboole_0(A_887,k2_xboole_0(B_888,C_889)),k2_xboole_0(B_888,C_889)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28])).

tff(c_41318,plain,(
    ! [A_887,A_35,B_36] : r1_tarski(k3_xboole_0(A_887,A_35),k2_xboole_0(k3_xboole_0(A_35,B_36),k4_xboole_0(A_35,B_36))) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_41297])).

tff(c_41343,plain,(
    ! [A_887,A_35] : r1_tarski(k3_xboole_0(A_887,A_35),A_35) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_41318])).

tff(c_43755,plain,(
    ! [A_972,B_973] : r1_tarski(A_972,k2_xboole_0(B_973,A_972)) ),
    inference(superposition,[status(thm),theory(equality)],[c_43695,c_41343])).

tff(c_41422,plain,(
    ! [A_892,C_893,B_894] :
      ( r1_xboole_0(A_892,C_893)
      | ~ r1_xboole_0(B_894,C_893)
      | ~ r1_tarski(A_892,B_894) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_44400,plain,(
    ! [A_991] :
      ( r1_xboole_0(A_991,'#skF_3')
      | ~ r1_tarski(A_991,k2_xboole_0('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_38203,c_41422])).

tff(c_44442,plain,(
    r1_xboole_0('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_43755,c_44400])).

tff(c_44460,plain,(
    k3_xboole_0('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44442,c_2])).

tff(c_44468,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42815,c_44460])).

tff(c_44470,plain,(
    ~ r1_xboole_0('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_42,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ r1_xboole_0('#skF_3','#skF_4')
    | r1_xboole_0('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_44600,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_44470,c_42])).

tff(c_44601,plain,(
    ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_44600])).

tff(c_45587,plain,(
    k3_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_45564,c_44601])).

tff(c_44469,plain,(
    r1_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_44477,plain,(
    r1_xboole_0(k2_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_44469,c_8])).

tff(c_45180,plain,(
    ! [A_1034,C_1035,B_1036] :
      ( r1_xboole_0(A_1034,C_1035)
      | ~ r1_xboole_0(B_1036,C_1035)
      | ~ r1_tarski(A_1034,B_1036) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_45708,plain,(
    ! [A_1064] :
      ( r1_xboole_0(A_1064,'#skF_3')
      | ~ r1_tarski(A_1064,k2_xboole_0('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_44477,c_45180])).

tff(c_45745,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_45708])).

tff(c_45752,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_45745,c_2])).

tff(c_45760,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45587,c_45752])).

tff(c_45761,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_44600])).

tff(c_47329,plain,(
    k3_xboole_0('#skF_5','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_47306,c_45761])).

tff(c_44535,plain,(
    ! [A_996,B_997,C_998] : r1_tarski(k3_xboole_0(A_996,B_997),k2_xboole_0(A_996,C_998)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_44555,plain,(
    ! [A_999,B_1000] : r1_tarski(k3_xboole_0(A_999,B_1000),A_999) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_44535])).

tff(c_44565,plain,(
    ! [A_999,B_1000] : k2_xboole_0(k3_xboole_0(A_999,B_1000),A_999) = A_999 ),
    inference(resolution,[status(thm)],[c_44555,c_20])).

tff(c_46073,plain,(
    ! [A_1077,B_1078] : k2_xboole_0(k3_xboole_0(A_1077,B_1078),k4_xboole_0(A_1077,B_1078)) = A_1077 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_46355,plain,(
    ! [A_1091] : k2_xboole_0(k3_xboole_0(A_1091,A_1091),k1_xboole_0) = A_1091 ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_46073])).

tff(c_45782,plain,(
    ! [A_1065,B_1066] :
      ( r2_hidden('#skF_1'(A_1065,B_1066),B_1066)
      | r1_xboole_0(A_1065,B_1066) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_44476,plain,(
    k3_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44469,c_2])).

tff(c_44584,plain,(
    ! [A_1001,B_1002,C_1003] :
      ( ~ r1_xboole_0(A_1001,B_1002)
      | ~ r2_hidden(C_1003,k3_xboole_0(A_1001,B_1002)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_44590,plain,(
    ! [C_1003] :
      ( ~ r1_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5'))
      | ~ r2_hidden(C_1003,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44476,c_44584])).

tff(c_44594,plain,(
    ! [C_1003] : ~ r2_hidden(C_1003,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44469,c_44590])).

tff(c_45793,plain,(
    ! [A_1067] : r1_xboole_0(A_1067,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_45782,c_44594])).

tff(c_45870,plain,(
    ! [A_1069] : k3_xboole_0(A_1069,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_45793,c_2])).

tff(c_45884,plain,(
    ! [A_1069] : k2_xboole_0(A_1069,k1_xboole_0) = A_1069 ),
    inference(superposition,[status(thm),theory(equality)],[c_45870,c_22])).

tff(c_46361,plain,(
    ! [A_1091] : k3_xboole_0(A_1091,A_1091) = A_1091 ),
    inference(superposition,[status(thm),theory(equality)],[c_46355,c_45884])).

tff(c_47044,plain,(
    ! [A_1122,B_1123,C_1124] : k2_xboole_0(k3_xboole_0(A_1122,B_1123),k3_xboole_0(A_1122,C_1124)) = k3_xboole_0(A_1122,k2_xboole_0(B_1123,C_1124)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_47077,plain,(
    ! [A_1091,B_1123] : k3_xboole_0(A_1091,k2_xboole_0(B_1123,A_1091)) = k2_xboole_0(k3_xboole_0(A_1091,B_1123),A_1091) ),
    inference(superposition,[status(thm),theory(equality)],[c_46361,c_47044])).

tff(c_47212,plain,(
    ! [A_1130,B_1131] : k3_xboole_0(A_1130,k2_xboole_0(B_1131,A_1130)) = A_1130 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44565,c_47077])).

tff(c_46164,plain,(
    ! [A_1081,B_1082,C_1083] : r1_tarski(k3_xboole_0(A_1081,k2_xboole_0(B_1082,C_1083)),k2_xboole_0(B_1082,C_1083)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28])).

tff(c_46170,plain,(
    ! [A_1081,A_35,B_36] : r1_tarski(k3_xboole_0(A_1081,A_35),k2_xboole_0(k3_xboole_0(A_35,B_36),k4_xboole_0(A_35,B_36))) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_46164])).

tff(c_46205,plain,(
    ! [A_1081,A_35] : r1_tarski(k3_xboole_0(A_1081,A_35),A_35) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_46170])).

tff(c_47236,plain,(
    ! [A_1130,B_1131] : r1_tarski(A_1130,k2_xboole_0(B_1131,A_1130)) ),
    inference(superposition,[status(thm),theory(equality)],[c_47212,c_46205])).

tff(c_46391,plain,(
    ! [A_1092,C_1093,B_1094] :
      ( r1_xboole_0(A_1092,C_1093)
      | ~ r1_xboole_0(B_1094,C_1093)
      | ~ r1_tarski(A_1092,B_1094) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_47368,plain,(
    ! [A_1136] :
      ( r1_xboole_0(A_1136,'#skF_3')
      | ~ r1_tarski(A_1136,k2_xboole_0('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_44477,c_46391])).

tff(c_47401,plain,(
    r1_xboole_0('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_47236,c_47368])).

tff(c_47418,plain,(
    k3_xboole_0('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_47401,c_2])).

tff(c_47426,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47329,c_47418])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:10:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.65/5.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.65/5.52  
% 12.65/5.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.65/5.52  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2 > #skF_1
% 12.65/5.52  
% 12.65/5.52  %Foreground sorts:
% 12.65/5.52  
% 12.65/5.52  
% 12.65/5.52  %Background operators:
% 12.65/5.52  
% 12.65/5.52  
% 12.65/5.52  %Foreground operators:
% 12.65/5.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.65/5.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.65/5.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.65/5.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.65/5.52  tff('#skF_7', type, '#skF_7': $i).
% 12.65/5.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.65/5.52  tff('#skF_5', type, '#skF_5': $i).
% 12.65/5.52  tff('#skF_6', type, '#skF_6': $i).
% 12.65/5.52  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 12.65/5.52  tff('#skF_3', type, '#skF_3': $i).
% 12.65/5.52  tff('#skF_8', type, '#skF_8': $i).
% 12.65/5.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.65/5.52  tff('#skF_4', type, '#skF_4': $i).
% 12.65/5.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.65/5.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 12.65/5.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.65/5.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.65/5.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.65/5.52  
% 12.79/5.55  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 12.79/5.55  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 12.79/5.55  tff(f_112, negated_conjecture, ~(![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 12.79/5.55  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 12.79/5.55  tff(f_67, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 12.79/5.55  tff(f_73, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 12.79/5.55  tff(f_75, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_xboole_1)).
% 12.79/5.55  tff(f_95, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 12.79/5.55  tff(f_71, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 12.79/5.55  tff(f_85, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 12.79/5.55  tff(f_87, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 12.79/5.55  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 12.79/5.55  tff(f_77, axiom, (![A, B, C]: r1_tarski(k3_xboole_0(A, B), k2_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_xboole_1)).
% 12.79/5.55  tff(f_79, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 12.79/5.55  tff(f_93, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 12.79/5.55  tff(c_44493, plain, (![A_992, B_993]: (r1_xboole_0(A_992, B_993) | k3_xboole_0(A_992, B_993)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.79/5.55  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.79/5.55  tff(c_47306, plain, (![B_1132, A_1133]: (r1_xboole_0(B_1132, A_1133) | k3_xboole_0(A_1133, B_1132)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_44493, c_8])).
% 12.79/5.55  tff(c_45564, plain, (![B_1057, A_1058]: (r1_xboole_0(B_1057, A_1058) | k3_xboole_0(A_1058, B_1057)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_44493, c_8])).
% 12.79/5.55  tff(c_144, plain, (![A_55, B_56]: (r1_xboole_0(A_55, B_56) | k3_xboole_0(A_55, B_56)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.79/5.55  tff(c_42797, plain, (![B_941, A_942]: (r1_xboole_0(B_941, A_942) | k3_xboole_0(A_942, B_941)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_144, c_8])).
% 12.79/5.55  tff(c_40117, plain, (![B_847, A_848]: (r1_xboole_0(B_847, A_848) | k3_xboole_0(A_848, B_847)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_144, c_8])).
% 12.79/5.55  tff(c_29875, plain, (![B_623, A_624]: (r1_xboole_0(B_623, A_624) | k3_xboole_0(A_624, B_623)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_144, c_8])).
% 12.79/5.55  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.79/5.55  tff(c_44, plain, (r1_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5')) | r1_xboole_0('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_112])).
% 12.79/5.55  tff(c_197, plain, (r1_xboole_0('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_44])).
% 12.79/5.55  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.79/5.55  tff(c_203, plain, (k3_xboole_0('#skF_6', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_197, c_2])).
% 12.79/5.55  tff(c_403, plain, (![A_70, B_71]: (r2_hidden('#skF_1'(A_70, B_71), B_71) | r1_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.79/5.55  tff(c_358, plain, (![A_66, B_67, C_68]: (~r1_xboole_0(A_66, B_67) | ~r2_hidden(C_68, k3_xboole_0(A_66, B_67)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 12.79/5.55  tff(c_364, plain, (![C_68]: (~r1_xboole_0('#skF_6', '#skF_7') | ~r2_hidden(C_68, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_203, c_358])).
% 12.79/5.55  tff(c_374, plain, (![C_68]: (~r2_hidden(C_68, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_197, c_364])).
% 12.79/5.55  tff(c_414, plain, (![A_72]: (r1_xboole_0(A_72, k1_xboole_0))), inference(resolution, [status(thm)], [c_403, c_374])).
% 12.79/5.55  tff(c_431, plain, (![A_74]: (k3_xboole_0(A_74, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_414, c_2])).
% 12.79/5.55  tff(c_22, plain, (![A_19, B_20]: (k2_xboole_0(A_19, k3_xboole_0(A_19, B_20))=A_19)), inference(cnfTransformation, [status(thm)], [f_73])).
% 12.79/5.55  tff(c_448, plain, (![A_74]: (k2_xboole_0(A_74, k1_xboole_0)=A_74)), inference(superposition, [status(thm), theory('equality')], [c_431, c_22])).
% 12.79/5.55  tff(c_40, plain, (r1_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5')) | r1_xboole_0('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_112])).
% 12.79/5.55  tff(c_102, plain, (r1_xboole_0('#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_40])).
% 12.79/5.55  tff(c_108, plain, (k3_xboole_0('#skF_6', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_102, c_2])).
% 12.79/5.55  tff(c_1606, plain, (![A_122, B_123, C_124]: (k2_xboole_0(k3_xboole_0(A_122, B_123), k3_xboole_0(A_122, C_124))=k3_xboole_0(A_122, k2_xboole_0(B_123, C_124)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.79/5.55  tff(c_1681, plain, (![B_123]: (k3_xboole_0('#skF_6', k2_xboole_0(B_123, '#skF_8'))=k2_xboole_0(k3_xboole_0('#skF_6', B_123), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_108, c_1606])).
% 12.79/5.55  tff(c_1706, plain, (![B_123]: (k3_xboole_0('#skF_6', k2_xboole_0(B_123, '#skF_8'))=k3_xboole_0('#skF_6', B_123))), inference(demodulation, [status(thm), theory('equality')], [c_448, c_1681])).
% 12.79/5.55  tff(c_48, plain, (r1_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5')) | ~r1_xboole_0('#skF_6', k2_xboole_0('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 12.79/5.55  tff(c_455, plain, (~r1_xboole_0('#skF_6', k2_xboole_0('#skF_7', '#skF_8'))), inference(splitLeft, [status(thm)], [c_48])).
% 12.79/5.55  tff(c_619, plain, (k3_xboole_0('#skF_6', k2_xboole_0('#skF_7', '#skF_8'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_455])).
% 12.79/5.55  tff(c_24491, plain, (k3_xboole_0('#skF_6', '#skF_7')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1706, c_619])).
% 12.79/5.55  tff(c_24494, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_203, c_24491])).
% 12.79/5.55  tff(c_24496, plain, (r1_xboole_0('#skF_6', k2_xboole_0('#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_48])).
% 12.79/5.55  tff(c_50, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_6', k2_xboole_0('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 12.79/5.55  tff(c_24681, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~r1_xboole_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24496, c_50])).
% 12.79/5.55  tff(c_24682, plain, (~r1_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_24681])).
% 12.79/5.55  tff(c_24686, plain, (k3_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_24682])).
% 12.79/5.55  tff(c_420, plain, (![A_72]: (k3_xboole_0(A_72, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_414, c_2])).
% 12.79/5.55  tff(c_24495, plain, (r1_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_48])).
% 12.79/5.55  tff(c_24662, plain, (k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_24495, c_2])).
% 12.79/5.55  tff(c_25732, plain, (![A_504, B_505, C_506]: (k2_xboole_0(k3_xboole_0(A_504, B_505), k3_xboole_0(A_504, C_506))=k3_xboole_0(A_504, k2_xboole_0(B_505, C_506)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.79/5.55  tff(c_38, plain, (![A_40, B_41]: (r1_tarski(A_40, k2_xboole_0(A_40, B_41)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 12.79/5.55  tff(c_28306, plain, (![A_572, B_573, C_574]: (r1_tarski(k3_xboole_0(A_572, B_573), k3_xboole_0(A_572, k2_xboole_0(B_573, C_574))))), inference(superposition, [status(thm), theory('equality')], [c_25732, c_38])).
% 12.79/5.55  tff(c_28382, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24662, c_28306])).
% 12.79/5.55  tff(c_20, plain, (![A_17, B_18]: (k2_xboole_0(A_17, B_18)=B_18 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.79/5.55  tff(c_28453, plain, (k2_xboole_0(k3_xboole_0('#skF_3', '#skF_4'), k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_28382, c_20])).
% 12.79/5.55  tff(c_32, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k2_xboole_0(A_33, B_34))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_85])).
% 12.79/5.55  tff(c_249, plain, (![A_62, B_63]: (k2_xboole_0(k3_xboole_0(A_62, B_63), k4_xboole_0(A_62, B_63))=A_62)), inference(cnfTransformation, [status(thm)], [f_87])).
% 12.79/5.55  tff(c_27335, plain, (![A_543, B_544]: (k2_xboole_0(k3_xboole_0(A_543, k2_xboole_0(A_543, B_544)), k1_xboole_0)=A_543)), inference(superposition, [status(thm), theory('equality')], [c_32, c_249])).
% 12.79/5.55  tff(c_27389, plain, (![A_543, B_544]: (k3_xboole_0(A_543, k2_xboole_0(A_543, B_544))=A_543)), inference(superposition, [status(thm), theory('equality')], [c_448, c_27335])).
% 12.79/5.55  tff(c_28472, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_4'), k1_xboole_0)=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_28453, c_27389])).
% 12.79/5.55  tff(c_28495, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_420, c_28472])).
% 12.79/5.55  tff(c_28497, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24686, c_28495])).
% 12.79/5.55  tff(c_28498, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_24681])).
% 12.79/5.55  tff(c_29890, plain, (k3_xboole_0('#skF_5', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_29875, c_28498])).
% 12.79/5.55  tff(c_6, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.79/5.55  tff(c_174, plain, (![A_59, B_60, C_61]: (r1_tarski(k3_xboole_0(A_59, B_60), k2_xboole_0(A_59, C_61)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 12.79/5.55  tff(c_285, plain, (![A_64, B_65]: (r1_tarski(k3_xboole_0(A_64, B_65), A_64))), inference(superposition, [status(thm), theory('equality')], [c_6, c_174])).
% 12.79/5.55  tff(c_301, plain, (![A_64, B_65]: (k2_xboole_0(k3_xboole_0(A_64, B_65), A_64)=A_64)), inference(resolution, [status(thm)], [c_285, c_20])).
% 12.79/5.55  tff(c_67, plain, (![A_48, B_49]: (k4_xboole_0(A_48, k2_xboole_0(A_48, B_49))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_85])).
% 12.79/5.55  tff(c_74, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_67])).
% 12.79/5.55  tff(c_28769, plain, (![A_585]: (k2_xboole_0(k3_xboole_0(A_585, A_585), k1_xboole_0)=A_585)), inference(superposition, [status(thm), theory('equality')], [c_74, c_249])).
% 12.79/5.55  tff(c_28775, plain, (![A_585]: (k3_xboole_0(A_585, A_585)=A_585)), inference(superposition, [status(thm), theory('equality')], [c_28769, c_448])).
% 12.79/5.55  tff(c_29525, plain, (![A_614, B_615, C_616]: (k2_xboole_0(k3_xboole_0(A_614, B_615), k3_xboole_0(A_614, C_616))=k3_xboole_0(A_614, k2_xboole_0(B_615, C_616)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.79/5.55  tff(c_29564, plain, (![A_585, B_615]: (k3_xboole_0(A_585, k2_xboole_0(B_615, A_585))=k2_xboole_0(k3_xboole_0(A_585, B_615), A_585))), inference(superposition, [status(thm), theory('equality')], [c_28775, c_29525])).
% 12.79/5.55  tff(c_32335, plain, (![A_685, B_686]: (k3_xboole_0(A_685, k2_xboole_0(B_686, A_685))=A_685)), inference(demodulation, [status(thm), theory('equality')], [c_301, c_29564])).
% 12.79/5.55  tff(c_34, plain, (![A_35, B_36]: (k2_xboole_0(k3_xboole_0(A_35, B_36), k4_xboole_0(A_35, B_36))=A_35)), inference(cnfTransformation, [status(thm)], [f_87])).
% 12.79/5.55  tff(c_24, plain, (![A_21, B_22, C_23]: (k2_xboole_0(k3_xboole_0(A_21, B_22), k3_xboole_0(A_21, C_23))=k3_xboole_0(A_21, k2_xboole_0(B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.79/5.55  tff(c_28, plain, (![A_27, B_28, C_29]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_27, B_28), k3_xboole_0(A_27, C_29)), k2_xboole_0(B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.79/5.55  tff(c_29063, plain, (![A_596, B_597, C_598]: (r1_tarski(k3_xboole_0(A_596, k2_xboole_0(B_597, C_598)), k2_xboole_0(B_597, C_598)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28])).
% 12.79/5.55  tff(c_29100, plain, (![A_596, A_35, B_36]: (r1_tarski(k3_xboole_0(A_596, A_35), k2_xboole_0(k3_xboole_0(A_35, B_36), k4_xboole_0(A_35, B_36))))), inference(superposition, [status(thm), theory('equality')], [c_34, c_29063])).
% 12.79/5.55  tff(c_29127, plain, (![A_596, A_35]: (r1_tarski(k3_xboole_0(A_596, A_35), A_35))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_29100])).
% 12.79/5.55  tff(c_32411, plain, (![A_685, B_686]: (r1_tarski(A_685, k2_xboole_0(B_686, A_685)))), inference(superposition, [status(thm), theory('equality')], [c_32335, c_29127])).
% 12.79/5.55  tff(c_24663, plain, (r1_xboole_0(k2_xboole_0('#skF_4', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_24495, c_8])).
% 12.79/5.55  tff(c_28805, plain, (![A_586, C_587, B_588]: (r1_xboole_0(A_586, C_587) | ~r1_xboole_0(B_588, C_587) | ~r1_tarski(A_586, B_588))), inference(cnfTransformation, [status(thm)], [f_93])).
% 12.79/5.55  tff(c_38123, plain, (![A_767]: (r1_xboole_0(A_767, '#skF_3') | ~r1_tarski(A_767, k2_xboole_0('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_24663, c_28805])).
% 12.79/5.55  tff(c_38166, plain, (r1_xboole_0('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_32411, c_38123])).
% 12.79/5.55  tff(c_38182, plain, (k3_xboole_0('#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_38166, c_2])).
% 12.79/5.55  tff(c_38190, plain, $false, inference(negUnitSimplification, [status(thm)], [c_29890, c_38182])).
% 12.79/5.55  tff(c_38192, plain, (~r1_xboole_0('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_44])).
% 12.79/5.55  tff(c_46, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~r1_xboole_0('#skF_3', '#skF_4') | r1_xboole_0('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_112])).
% 12.79/5.55  tff(c_38270, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~r1_xboole_0('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_38192, c_46])).
% 12.79/5.55  tff(c_38271, plain, (~r1_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_38270])).
% 12.79/5.55  tff(c_40140, plain, (k3_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_40117, c_38271])).
% 12.79/5.55  tff(c_38191, plain, (r1_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_44])).
% 12.79/5.55  tff(c_38203, plain, (r1_xboole_0(k2_xboole_0('#skF_4', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_38191, c_8])).
% 12.79/5.55  tff(c_38924, plain, (![A_801, C_802, B_803]: (r1_xboole_0(A_801, C_802) | ~r1_xboole_0(B_803, C_802) | ~r1_tarski(A_801, B_803))), inference(cnfTransformation, [status(thm)], [f_93])).
% 12.79/5.55  tff(c_40773, plain, (![A_870]: (r1_xboole_0(A_870, '#skF_3') | ~r1_tarski(A_870, k2_xboole_0('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_38203, c_38924])).
% 12.79/5.55  tff(c_40825, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_40773])).
% 12.79/5.55  tff(c_40832, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_40825, c_2])).
% 12.79/5.55  tff(c_40840, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40140, c_40832])).
% 12.79/5.55  tff(c_40841, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_38270])).
% 12.79/5.55  tff(c_42815, plain, (k3_xboole_0('#skF_5', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_42797, c_40841])).
% 12.79/5.55  tff(c_38204, plain, (![A_768, B_769]: (r1_tarski(k3_xboole_0(A_768, B_769), A_768))), inference(superposition, [status(thm), theory('equality')], [c_6, c_174])).
% 12.79/5.55  tff(c_38214, plain, (![A_768, B_769]: (k2_xboole_0(k3_xboole_0(A_768, B_769), A_768)=A_768)), inference(resolution, [status(thm)], [c_38204, c_20])).
% 12.79/5.55  tff(c_41086, plain, (![A_882, B_883]: (k2_xboole_0(k3_xboole_0(A_882, B_883), k4_xboole_0(A_882, B_883))=A_882)), inference(cnfTransformation, [status(thm)], [f_87])).
% 12.79/5.55  tff(c_41635, plain, (![A_906]: (k2_xboole_0(k3_xboole_0(A_906, A_906), k1_xboole_0)=A_906)), inference(superposition, [status(thm), theory('equality')], [c_74, c_41086])).
% 12.79/5.55  tff(c_12, plain, (![A_7, B_8]: (r2_hidden('#skF_1'(A_7, B_8), B_8) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.79/5.55  tff(c_40862, plain, (![A_871, B_872, C_873]: (~r1_xboole_0(A_871, B_872) | ~r2_hidden(C_873, k3_xboole_0(A_871, B_872)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 12.79/5.55  tff(c_40872, plain, (![C_873]: (~r1_xboole_0('#skF_6', '#skF_8') | ~r2_hidden(C_873, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_108, c_40862])).
% 12.79/5.55  tff(c_40878, plain, (![C_874]: (~r2_hidden(C_874, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_40872])).
% 12.79/5.55  tff(c_40884, plain, (![A_875]: (r1_xboole_0(A_875, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_40878])).
% 12.79/5.55  tff(c_41006, plain, (![A_879]: (k3_xboole_0(A_879, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40884, c_2])).
% 12.79/5.55  tff(c_41020, plain, (![A_879]: (k2_xboole_0(A_879, k1_xboole_0)=A_879)), inference(superposition, [status(thm), theory('equality')], [c_41006, c_22])).
% 12.79/5.55  tff(c_41645, plain, (![A_906]: (k3_xboole_0(A_906, A_906)=A_906)), inference(superposition, [status(thm), theory('equality')], [c_41635, c_41020])).
% 12.79/5.55  tff(c_42124, plain, (![A_924, B_925, C_926]: (k2_xboole_0(k3_xboole_0(A_924, B_925), k3_xboole_0(A_924, C_926))=k3_xboole_0(A_924, k2_xboole_0(B_925, C_926)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.79/5.55  tff(c_42159, plain, (![A_906, B_925]: (k3_xboole_0(A_906, k2_xboole_0(B_925, A_906))=k2_xboole_0(k3_xboole_0(A_906, B_925), A_906))), inference(superposition, [status(thm), theory('equality')], [c_41645, c_42124])).
% 12.79/5.55  tff(c_43695, plain, (![A_972, B_973]: (k3_xboole_0(A_972, k2_xboole_0(B_973, A_972))=A_972)), inference(demodulation, [status(thm), theory('equality')], [c_38214, c_42159])).
% 12.79/5.55  tff(c_41297, plain, (![A_887, B_888, C_889]: (r1_tarski(k3_xboole_0(A_887, k2_xboole_0(B_888, C_889)), k2_xboole_0(B_888, C_889)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28])).
% 12.79/5.55  tff(c_41318, plain, (![A_887, A_35, B_36]: (r1_tarski(k3_xboole_0(A_887, A_35), k2_xboole_0(k3_xboole_0(A_35, B_36), k4_xboole_0(A_35, B_36))))), inference(superposition, [status(thm), theory('equality')], [c_34, c_41297])).
% 12.79/5.55  tff(c_41343, plain, (![A_887, A_35]: (r1_tarski(k3_xboole_0(A_887, A_35), A_35))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_41318])).
% 12.79/5.55  tff(c_43755, plain, (![A_972, B_973]: (r1_tarski(A_972, k2_xboole_0(B_973, A_972)))), inference(superposition, [status(thm), theory('equality')], [c_43695, c_41343])).
% 12.79/5.55  tff(c_41422, plain, (![A_892, C_893, B_894]: (r1_xboole_0(A_892, C_893) | ~r1_xboole_0(B_894, C_893) | ~r1_tarski(A_892, B_894))), inference(cnfTransformation, [status(thm)], [f_93])).
% 12.79/5.55  tff(c_44400, plain, (![A_991]: (r1_xboole_0(A_991, '#skF_3') | ~r1_tarski(A_991, k2_xboole_0('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_38203, c_41422])).
% 12.79/5.55  tff(c_44442, plain, (r1_xboole_0('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_43755, c_44400])).
% 12.79/5.55  tff(c_44460, plain, (k3_xboole_0('#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_44442, c_2])).
% 12.79/5.55  tff(c_44468, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42815, c_44460])).
% 12.79/5.55  tff(c_44470, plain, (~r1_xboole_0('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_40])).
% 12.79/5.55  tff(c_42, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~r1_xboole_0('#skF_3', '#skF_4') | r1_xboole_0('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_112])).
% 12.79/5.55  tff(c_44600, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~r1_xboole_0('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_44470, c_42])).
% 12.79/5.55  tff(c_44601, plain, (~r1_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_44600])).
% 12.79/5.55  tff(c_45587, plain, (k3_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_45564, c_44601])).
% 12.79/5.55  tff(c_44469, plain, (r1_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_40])).
% 12.79/5.55  tff(c_44477, plain, (r1_xboole_0(k2_xboole_0('#skF_4', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_44469, c_8])).
% 12.79/5.55  tff(c_45180, plain, (![A_1034, C_1035, B_1036]: (r1_xboole_0(A_1034, C_1035) | ~r1_xboole_0(B_1036, C_1035) | ~r1_tarski(A_1034, B_1036))), inference(cnfTransformation, [status(thm)], [f_93])).
% 12.79/5.55  tff(c_45708, plain, (![A_1064]: (r1_xboole_0(A_1064, '#skF_3') | ~r1_tarski(A_1064, k2_xboole_0('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_44477, c_45180])).
% 12.79/5.55  tff(c_45745, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_45708])).
% 12.79/5.55  tff(c_45752, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_45745, c_2])).
% 12.79/5.55  tff(c_45760, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45587, c_45752])).
% 12.79/5.55  tff(c_45761, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_44600])).
% 12.79/5.55  tff(c_47329, plain, (k3_xboole_0('#skF_5', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_47306, c_45761])).
% 12.79/5.55  tff(c_44535, plain, (![A_996, B_997, C_998]: (r1_tarski(k3_xboole_0(A_996, B_997), k2_xboole_0(A_996, C_998)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 12.79/5.55  tff(c_44555, plain, (![A_999, B_1000]: (r1_tarski(k3_xboole_0(A_999, B_1000), A_999))), inference(superposition, [status(thm), theory('equality')], [c_22, c_44535])).
% 12.79/5.55  tff(c_44565, plain, (![A_999, B_1000]: (k2_xboole_0(k3_xboole_0(A_999, B_1000), A_999)=A_999)), inference(resolution, [status(thm)], [c_44555, c_20])).
% 12.79/5.55  tff(c_46073, plain, (![A_1077, B_1078]: (k2_xboole_0(k3_xboole_0(A_1077, B_1078), k4_xboole_0(A_1077, B_1078))=A_1077)), inference(cnfTransformation, [status(thm)], [f_87])).
% 12.79/5.55  tff(c_46355, plain, (![A_1091]: (k2_xboole_0(k3_xboole_0(A_1091, A_1091), k1_xboole_0)=A_1091)), inference(superposition, [status(thm), theory('equality')], [c_74, c_46073])).
% 12.79/5.55  tff(c_45782, plain, (![A_1065, B_1066]: (r2_hidden('#skF_1'(A_1065, B_1066), B_1066) | r1_xboole_0(A_1065, B_1066))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.79/5.55  tff(c_44476, plain, (k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_44469, c_2])).
% 12.79/5.55  tff(c_44584, plain, (![A_1001, B_1002, C_1003]: (~r1_xboole_0(A_1001, B_1002) | ~r2_hidden(C_1003, k3_xboole_0(A_1001, B_1002)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 12.79/5.55  tff(c_44590, plain, (![C_1003]: (~r1_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5')) | ~r2_hidden(C_1003, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_44476, c_44584])).
% 12.79/5.55  tff(c_44594, plain, (![C_1003]: (~r2_hidden(C_1003, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_44469, c_44590])).
% 12.79/5.55  tff(c_45793, plain, (![A_1067]: (r1_xboole_0(A_1067, k1_xboole_0))), inference(resolution, [status(thm)], [c_45782, c_44594])).
% 12.79/5.55  tff(c_45870, plain, (![A_1069]: (k3_xboole_0(A_1069, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_45793, c_2])).
% 12.79/5.55  tff(c_45884, plain, (![A_1069]: (k2_xboole_0(A_1069, k1_xboole_0)=A_1069)), inference(superposition, [status(thm), theory('equality')], [c_45870, c_22])).
% 12.79/5.55  tff(c_46361, plain, (![A_1091]: (k3_xboole_0(A_1091, A_1091)=A_1091)), inference(superposition, [status(thm), theory('equality')], [c_46355, c_45884])).
% 12.79/5.55  tff(c_47044, plain, (![A_1122, B_1123, C_1124]: (k2_xboole_0(k3_xboole_0(A_1122, B_1123), k3_xboole_0(A_1122, C_1124))=k3_xboole_0(A_1122, k2_xboole_0(B_1123, C_1124)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.79/5.55  tff(c_47077, plain, (![A_1091, B_1123]: (k3_xboole_0(A_1091, k2_xboole_0(B_1123, A_1091))=k2_xboole_0(k3_xboole_0(A_1091, B_1123), A_1091))), inference(superposition, [status(thm), theory('equality')], [c_46361, c_47044])).
% 12.79/5.55  tff(c_47212, plain, (![A_1130, B_1131]: (k3_xboole_0(A_1130, k2_xboole_0(B_1131, A_1130))=A_1130)), inference(demodulation, [status(thm), theory('equality')], [c_44565, c_47077])).
% 12.79/5.55  tff(c_46164, plain, (![A_1081, B_1082, C_1083]: (r1_tarski(k3_xboole_0(A_1081, k2_xboole_0(B_1082, C_1083)), k2_xboole_0(B_1082, C_1083)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28])).
% 12.79/5.55  tff(c_46170, plain, (![A_1081, A_35, B_36]: (r1_tarski(k3_xboole_0(A_1081, A_35), k2_xboole_0(k3_xboole_0(A_35, B_36), k4_xboole_0(A_35, B_36))))), inference(superposition, [status(thm), theory('equality')], [c_34, c_46164])).
% 12.79/5.55  tff(c_46205, plain, (![A_1081, A_35]: (r1_tarski(k3_xboole_0(A_1081, A_35), A_35))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_46170])).
% 12.79/5.55  tff(c_47236, plain, (![A_1130, B_1131]: (r1_tarski(A_1130, k2_xboole_0(B_1131, A_1130)))), inference(superposition, [status(thm), theory('equality')], [c_47212, c_46205])).
% 12.79/5.55  tff(c_46391, plain, (![A_1092, C_1093, B_1094]: (r1_xboole_0(A_1092, C_1093) | ~r1_xboole_0(B_1094, C_1093) | ~r1_tarski(A_1092, B_1094))), inference(cnfTransformation, [status(thm)], [f_93])).
% 12.79/5.55  tff(c_47368, plain, (![A_1136]: (r1_xboole_0(A_1136, '#skF_3') | ~r1_tarski(A_1136, k2_xboole_0('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_44477, c_46391])).
% 12.79/5.55  tff(c_47401, plain, (r1_xboole_0('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_47236, c_47368])).
% 12.79/5.55  tff(c_47418, plain, (k3_xboole_0('#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_47401, c_2])).
% 12.79/5.55  tff(c_47426, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47329, c_47418])).
% 12.79/5.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.79/5.55  
% 12.79/5.55  Inference rules
% 12.79/5.55  ----------------------
% 12.79/5.55  #Ref     : 0
% 12.79/5.55  #Sup     : 11932
% 12.79/5.55  #Fact    : 0
% 12.79/5.55  #Define  : 0
% 12.79/5.55  #Split   : 25
% 12.79/5.55  #Chain   : 0
% 12.79/5.55  #Close   : 0
% 12.79/5.55  
% 12.79/5.55  Ordering : KBO
% 12.79/5.55  
% 12.79/5.55  Simplification rules
% 12.79/5.55  ----------------------
% 12.79/5.55  #Subsume      : 1436
% 12.79/5.55  #Demod        : 8741
% 12.79/5.55  #Tautology    : 8127
% 12.79/5.55  #SimpNegUnit  : 173
% 12.79/5.55  #BackRed      : 46
% 12.79/5.55  
% 12.79/5.55  #Partial instantiations: 0
% 12.79/5.55  #Strategies tried      : 1
% 12.79/5.55  
% 12.79/5.55  Timing (in seconds)
% 12.79/5.55  ----------------------
% 12.79/5.55  Preprocessing        : 0.33
% 12.79/5.55  Parsing              : 0.19
% 12.79/5.55  CNF conversion       : 0.02
% 12.79/5.55  Main loop            : 4.40
% 12.79/5.55  Inferencing          : 0.98
% 12.79/5.55  Reduction            : 2.15
% 12.79/5.55  Demodulation         : 1.73
% 12.79/5.55  BG Simplification    : 0.09
% 12.79/5.55  Subsumption          : 0.91
% 12.79/5.55  Abstraction          : 0.14
% 12.79/5.55  MUC search           : 0.00
% 12.79/5.55  Cooper               : 0.00
% 12.79/5.55  Total                : 4.79
% 12.79/5.55  Index Insertion      : 0.00
% 12.79/5.55  Index Deletion       : 0.00
% 12.79/5.55  Index Matching       : 0.00
% 12.79/5.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
