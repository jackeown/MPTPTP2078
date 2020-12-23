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
% DateTime   : Thu Dec  3 09:54:16 EST 2020

% Result     : Theorem 27.50s
% Output     : CNFRefutation 27.64s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 509 expanded)
%              Number of leaves         :   23 ( 175 expanded)
%              Depth                    :   14
%              Number of atoms          :  239 (1044 expanded)
%              Number of equality atoms :   99 ( 587 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
          | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
        & ~ r1_tarski(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_70,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k3_xboole_0(A,B),C) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t122_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

tff(c_32,plain,
    ( '#skF_2' != '#skF_4'
    | '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_40,plain,(
    '#skF_3' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_38,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_274,plain,(
    ! [A_49,C_50,B_51] :
      ( r1_tarski(k2_zfmisc_1(A_49,C_50),k2_zfmisc_1(B_51,C_50))
      | ~ r1_tarski(A_49,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_285,plain,(
    ! [A_49] :
      ( r1_tarski(k2_zfmisc_1(A_49,'#skF_4'),k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_49,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_274])).

tff(c_945,plain,(
    ! [A_72,B_73,C_74] :
      ( ~ r1_tarski(k2_zfmisc_1(A_72,B_73),k2_zfmisc_1(A_72,C_74))
      | r1_tarski(B_73,C_74)
      | k1_xboole_0 = A_72 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_949,plain,
    ( r1_tarski('#skF_4','#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_285,c_945])).

tff(c_969,plain,
    ( r1_tarski('#skF_4','#skF_2')
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_949])).

tff(c_976,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_969])).

tff(c_493,plain,(
    ! [C_58,A_59,B_60] :
      ( r1_tarski(k2_zfmisc_1(C_58,A_59),k2_zfmisc_1(C_58,B_60))
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_501,plain,(
    ! [B_60] :
      ( r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3',B_60))
      | ~ r1_tarski('#skF_4',B_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_493])).

tff(c_1126,plain,(
    ! [B_78,A_79,C_80] :
      ( ~ r1_tarski(k2_zfmisc_1(B_78,A_79),k2_zfmisc_1(C_80,A_79))
      | r1_tarski(B_78,C_80)
      | k1_xboole_0 = A_79 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1130,plain,
    ( r1_tarski('#skF_1','#skF_3')
    | k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_501,c_1126])).

tff(c_1154,plain,(
    ~ r1_tarski('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_976,c_1130])).

tff(c_10,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_50,plain,(
    ! [A_28,B_29] : r1_tarski(k3_xboole_0(A_28,B_29),A_28) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_53,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_50])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_504,plain,(
    ! [A_59] :
      ( r1_tarski(k2_zfmisc_1('#skF_3',A_59),k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_59,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_493])).

tff(c_1134,plain,
    ( r1_tarski('#skF_3','#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_504,c_1126])).

tff(c_1157,plain,
    ( r1_tarski('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1134])).

tff(c_1164,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1157])).

tff(c_30,plain,(
    ! [A_22,C_24,B_23,D_25] : k3_xboole_0(k2_zfmisc_1(A_22,C_24),k2_zfmisc_1(B_23,D_25)) = k2_zfmisc_1(k3_xboole_0(A_22,B_23),k3_xboole_0(C_24,D_25)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1658,plain,(
    ! [A_100,C_101,B_102,D_103] : k3_xboole_0(k2_zfmisc_1(A_100,C_101),k2_zfmisc_1(B_102,D_103)) = k2_zfmisc_1(k3_xboole_0(A_100,B_102),k3_xboole_0(C_101,D_103)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1751,plain,(
    ! [A_100,C_101] : k3_xboole_0(k2_zfmisc_1(A_100,C_101),k2_zfmisc_1('#skF_1','#skF_2')) = k2_zfmisc_1(k3_xboole_0(A_100,'#skF_3'),k3_xboole_0(C_101,'#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1658])).

tff(c_26582,plain,(
    ! [A_374,C_375] : k2_zfmisc_1(k3_xboole_0(A_374,'#skF_3'),k3_xboole_0(C_375,'#skF_4')) = k2_zfmisc_1(k3_xboole_0(A_374,'#skF_1'),k3_xboole_0(C_375,'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1751])).

tff(c_12,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1937,plain,(
    ! [A_109,B_110,C_111,D_112] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_109,B_110),k3_xboole_0(C_111,D_112)),k2_zfmisc_1(A_109,C_111)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1658,c_12])).

tff(c_2020,plain,(
    ! [A_109,B_110,A_1,B_2] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_109,B_110),k3_xboole_0(A_1,B_2)),k2_zfmisc_1(A_109,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1937])).

tff(c_26853,plain,(
    ! [A_376,C_377] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_376,'#skF_1'),k3_xboole_0(C_377,'#skF_2')),k2_zfmisc_1(A_376,'#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_26582,c_2020])).

tff(c_26979,plain,(
    ! [C_378] : r1_tarski(k2_zfmisc_1('#skF_1',k3_xboole_0(C_378,'#skF_2')),k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_26853])).

tff(c_18,plain,(
    ! [A_13,B_14,C_15] :
      ( ~ r1_tarski(k2_zfmisc_1(A_13,B_14),k2_zfmisc_1(A_13,C_15))
      | r1_tarski(B_14,C_15)
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_26982,plain,(
    ! [C_378] :
      ( r1_tarski(k3_xboole_0(C_378,'#skF_2'),'#skF_4')
      | k1_xboole_0 = '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_26979,c_18])).

tff(c_27039,plain,(
    ! [C_379] : r1_tarski(k3_xboole_0(C_379,'#skF_2'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_26982])).

tff(c_27072,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_27039])).

tff(c_27078,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1164,c_27072])).

tff(c_27080,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_1157])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_27115,plain,(
    k3_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_27080,c_14])).

tff(c_27228,plain,(
    k3_xboole_0('#skF_4','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_27115])).

tff(c_27079,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_1157])).

tff(c_27108,plain,(
    k3_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_27079,c_14])).

tff(c_845,plain,(
    ! [C_68,A_69,B_70] : k3_xboole_0(k2_zfmisc_1(C_68,A_69),k2_zfmisc_1(C_68,B_70)) = k2_zfmisc_1(C_68,k3_xboole_0(A_69,B_70)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_29077,plain,(
    ! [C_427,B_428,A_429] : k3_xboole_0(k2_zfmisc_1(C_427,B_428),k2_zfmisc_1(C_427,A_429)) = k2_zfmisc_1(C_427,k3_xboole_0(A_429,B_428)) ),
    inference(superposition,[status(thm),theory(equality)],[c_845,c_2])).

tff(c_39751,plain,(
    ! [B_543] : k3_xboole_0(k2_zfmisc_1('#skF_3',B_543),k2_zfmisc_1('#skF_1','#skF_2')) = k2_zfmisc_1('#skF_3',k3_xboole_0('#skF_4',B_543)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_29077])).

tff(c_39802,plain,(
    ! [B_543] : k2_zfmisc_1(k3_xboole_0('#skF_3','#skF_1'),k3_xboole_0(B_543,'#skF_2')) = k2_zfmisc_1('#skF_3',k3_xboole_0('#skF_4',B_543)) ),
    inference(superposition,[status(thm),theory(equality)],[c_39751,c_30])).

tff(c_53750,plain,(
    ! [B_702] : k2_zfmisc_1('#skF_3',k3_xboole_0(B_702,'#skF_2')) = k2_zfmisc_1('#skF_3',k3_xboole_0('#skF_4',B_702)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27108,c_39802])).

tff(c_54149,plain,(
    k2_zfmisc_1('#skF_3',k3_xboole_0('#skF_4','#skF_4')) = k2_zfmisc_1('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_27228,c_53750])).

tff(c_54238,plain,(
    k2_zfmisc_1('#skF_3','#skF_2') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_10,c_54149])).

tff(c_22,plain,(
    ! [C_18,A_16,B_17] :
      ( r1_tarski(k2_zfmisc_1(C_18,A_16),k2_zfmisc_1(C_18,B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_959,plain,(
    ! [C_74] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3',C_74))
      | r1_tarski('#skF_4',C_74)
      | k1_xboole_0 = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_945])).

tff(c_29246,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_959])).

tff(c_29249,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29246,c_34])).

tff(c_35540,plain,(
    ! [B_505] : k3_xboole_0(k2_zfmisc_1('#skF_3',B_505),k2_zfmisc_1('#skF_1','#skF_2')) = k2_zfmisc_1('#skF_3',k3_xboole_0('#skF_4',B_505)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_29077])).

tff(c_35627,plain,(
    ! [B_505] : k2_zfmisc_1(k3_xboole_0('#skF_3','#skF_1'),k3_xboole_0(B_505,'#skF_2')) = k2_zfmisc_1('#skF_3',k3_xboole_0('#skF_4',B_505)) ),
    inference(superposition,[status(thm),theory(equality)],[c_35540,c_30])).

tff(c_35754,plain,(
    ! [B_506] : k2_zfmisc_1('#skF_3',k3_xboole_0(B_506,'#skF_2')) = k2_zfmisc_1('#skF_3',k3_xboole_0('#skF_4',B_506)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27108,c_35627])).

tff(c_35983,plain,(
    k2_zfmisc_1('#skF_3',k3_xboole_0('#skF_4','#skF_4')) = k2_zfmisc_1('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_27228,c_35754])).

tff(c_36041,plain,(
    k2_zfmisc_1('#skF_3','#skF_2') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_10,c_35983])).

tff(c_20,plain,(
    ! [B_14,A_13,C_15] :
      ( ~ r1_tarski(k2_zfmisc_1(B_14,A_13),k2_zfmisc_1(C_15,A_13))
      | r1_tarski(B_14,C_15)
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_36490,plain,(
    ! [B_510,A_511,C_512] :
      ( ~ r1_tarski(k2_zfmisc_1(B_510,A_511),k2_zfmisc_1(C_512,A_511))
      | r1_tarski(B_510,C_512)
      | A_511 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29246,c_20])).

tff(c_36496,plain,(
    ! [B_510] :
      ( ~ r1_tarski(k2_zfmisc_1(B_510,'#skF_2'),k2_zfmisc_1('#skF_1','#skF_2'))
      | r1_tarski(B_510,'#skF_3')
      | '#skF_2' = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36041,c_36490])).

tff(c_37314,plain,(
    ! [B_524] :
      ( ~ r1_tarski(k2_zfmisc_1(B_524,'#skF_2'),k2_zfmisc_1('#skF_1','#skF_2'))
      | r1_tarski(B_524,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_29249,c_36496])).

tff(c_37351,plain,
    ( r1_tarski('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_37314])).

tff(c_37375,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_37351])).

tff(c_37377,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_976,c_37375])).

tff(c_37378,plain,(
    ! [C_74] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3',C_74))
      | r1_tarski('#skF_4',C_74) ) ),
    inference(splitRight,[status(thm)],[c_959])).

tff(c_54307,plain,
    ( ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2'))
    | r1_tarski('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_54238,c_37378])).

tff(c_54397,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_54307])).

tff(c_54399,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1154,c_54397])).

tff(c_54401,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_969])).

tff(c_128,plain,(
    ! [A_41,B_42] :
      ( r2_xboole_0(A_41,B_42)
      | B_42 = A_41
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( ~ r2_xboole_0(B_12,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_139,plain,(
    ! [B_42,A_41] :
      ( ~ r1_tarski(B_42,A_41)
      | B_42 = A_41
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(resolution,[status(thm)],[c_128,c_16])).

tff(c_54410,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_54401,c_139])).

tff(c_54416,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_54410])).

tff(c_54418,plain,(
    ! [B_703,A_704,C_705] :
      ( ~ r1_tarski(k2_zfmisc_1(B_703,A_704),k2_zfmisc_1(C_705,A_704))
      | r1_tarski(B_703,C_705)
      | k1_xboole_0 = A_704 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_54422,plain,
    ( r1_tarski('#skF_3','#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_504,c_54418])).

tff(c_54442,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_54416,c_54422])).

tff(c_54435,plain,(
    ! [B_703] :
      ( ~ r1_tarski(k2_zfmisc_1(B_703,'#skF_4'),k2_zfmisc_1('#skF_1','#skF_2'))
      | r1_tarski(B_703,'#skF_3')
      | k1_xboole_0 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_54418])).

tff(c_56320,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_54435])).

tff(c_56324,plain,(
    '#skF_1' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56320,c_36])).

tff(c_54400,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_969])).

tff(c_54408,plain,(
    k3_xboole_0('#skF_4','#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_54400,c_14])).

tff(c_61,plain,(
    ! [B_35,A_36] : k3_xboole_0(B_35,A_36) = k3_xboole_0(A_36,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_76,plain,(
    ! [B_35,A_36] : r1_tarski(k3_xboole_0(B_35,A_36),A_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_12])).

tff(c_114,plain,(
    ! [A_39,B_40] :
      ( k3_xboole_0(A_39,B_40) = A_39
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_207,plain,(
    ! [B_47,A_48] : k3_xboole_0(k3_xboole_0(B_47,A_48),A_48) = k3_xboole_0(B_47,A_48) ),
    inference(resolution,[status(thm)],[c_76,c_114])).

tff(c_255,plain,(
    ! [A_1,B_2] : k3_xboole_0(k3_xboole_0(A_1,B_2),A_1) = k3_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_207])).

tff(c_54455,plain,(
    k3_xboole_0('#skF_2','#skF_4') = k3_xboole_0('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_54408,c_255])).

tff(c_54486,plain,(
    k3_xboole_0('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_54455])).

tff(c_145,plain,(
    ! [A_43,B_44] : k3_xboole_0(k3_xboole_0(A_43,B_44),A_43) = k3_xboole_0(A_43,B_44) ),
    inference(resolution,[status(thm)],[c_12,c_114])).

tff(c_179,plain,(
    ! [A_1,B_2] : k3_xboole_0(k3_xboole_0(A_1,B_2),B_2) = k3_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_145])).

tff(c_906,plain,(
    ! [A_69] : k3_xboole_0(k2_zfmisc_1('#skF_3',A_69),k2_zfmisc_1('#skF_1','#skF_2')) = k2_zfmisc_1('#skF_3',k3_xboole_0(A_69,'#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_845])).

tff(c_54417,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_54401,c_14])).

tff(c_56377,plain,(
    ! [A_755] : k3_xboole_0(k2_zfmisc_1('#skF_3',A_755),k2_zfmisc_1('#skF_1','#skF_2')) = k2_zfmisc_1('#skF_3',k3_xboole_0(A_755,'#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_845])).

tff(c_124,plain,(
    ! [B_35,A_36] : k3_xboole_0(k3_xboole_0(B_35,A_36),A_36) = k3_xboole_0(B_35,A_36) ),
    inference(resolution,[status(thm)],[c_76,c_114])).

tff(c_56448,plain,(
    ! [A_755] : k3_xboole_0(k2_zfmisc_1('#skF_3',k3_xboole_0(A_755,'#skF_4')),k2_zfmisc_1('#skF_1','#skF_2')) = k3_xboole_0(k2_zfmisc_1('#skF_3',A_755),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_56377,c_124])).

tff(c_70331,plain,(
    ! [A_914] : k2_zfmisc_1('#skF_3',k3_xboole_0('#skF_4',A_914)) = k2_zfmisc_1('#skF_1',k3_xboole_0('#skF_2',A_914)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_906,c_54417,c_30,c_2,c_56448])).

tff(c_70473,plain,(
    k2_zfmisc_1('#skF_1',k3_xboole_0('#skF_2','#skF_4')) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_70331])).

tff(c_70489,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k2_zfmisc_1('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_54486,c_70473])).

tff(c_55065,plain,(
    ! [C_717,A_718,B_719] : r1_tarski(k2_zfmisc_1(C_717,k3_xboole_0(A_718,B_719)),k2_zfmisc_1(C_717,A_718)) ),
    inference(superposition,[status(thm),theory(equality)],[c_845,c_12])).

tff(c_55124,plain,(
    ! [C_717,A_1,B_2] : r1_tarski(k2_zfmisc_1(C_717,k3_xboole_0(A_1,B_2)),k2_zfmisc_1(C_717,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_55065])).

tff(c_70540,plain,(
    ! [A_1] : r1_tarski(k2_zfmisc_1('#skF_1',k3_xboole_0(A_1,'#skF_2')),k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_70489,c_55124])).

tff(c_71564,plain,(
    ! [A_924,B_925,C_926] :
      ( ~ r1_tarski(k2_zfmisc_1(A_924,B_925),k2_zfmisc_1(A_924,C_926))
      | r1_tarski(B_925,C_926)
      | A_924 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56320,c_18])).

tff(c_71567,plain,(
    ! [A_1] :
      ( r1_tarski(k3_xboole_0(A_1,'#skF_2'),'#skF_4')
      | '#skF_1' = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_70540,c_71564])).

tff(c_71692,plain,(
    ! [A_927] : r1_tarski(k3_xboole_0(A_927,'#skF_2'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_56324,c_71567])).

tff(c_71727,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_71692])).

tff(c_71734,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54442,c_71727])).

tff(c_71736,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_54435])).

tff(c_54962,plain,(
    ! [A_713,C_714,B_715,D_716] : k3_xboole_0(k2_zfmisc_1(A_713,C_714),k2_zfmisc_1(B_715,D_716)) = k2_zfmisc_1(k3_xboole_0(A_713,B_715),k3_xboole_0(C_714,D_716)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_93184,plain,(
    ! [B_1134,D_1135,A_1136,C_1137] : k3_xboole_0(k2_zfmisc_1(B_1134,D_1135),k2_zfmisc_1(A_1136,C_1137)) = k2_zfmisc_1(k3_xboole_0(A_1136,B_1134),k3_xboole_0(C_1137,D_1135)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54962,c_2])).

tff(c_54694,plain,(
    ! [A_707,C_708,B_709] : k3_xboole_0(k2_zfmisc_1(A_707,C_708),k2_zfmisc_1(B_709,C_708)) = k2_zfmisc_1(k3_xboole_0(A_707,B_709),C_708) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_54760,plain,(
    ! [B_709] : k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1(B_709,'#skF_4')) = k2_zfmisc_1(k3_xboole_0('#skF_3',B_709),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_54694])).

tff(c_93238,plain,(
    ! [A_1136] : k2_zfmisc_1(k3_xboole_0(A_1136,'#skF_1'),k3_xboole_0('#skF_4','#skF_2')) = k2_zfmisc_1(k3_xboole_0('#skF_3',A_1136),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_93184,c_54760])).

tff(c_101760,plain,(
    ! [A_1229] : k2_zfmisc_1(k3_xboole_0(A_1229,'#skF_1'),'#skF_4') = k2_zfmisc_1(k3_xboole_0('#skF_3',A_1229),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54408,c_93238])).

tff(c_55184,plain,(
    ! [A_722,B_723,C_724] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_722,B_723),C_724),k2_zfmisc_1(A_722,C_724)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54694,c_12])).

tff(c_55243,plain,(
    ! [A_1,B_2,C_724] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_1,B_2),C_724),k2_zfmisc_1(B_2,C_724)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_55184])).

tff(c_102487,plain,(
    ! [A_1230] : r1_tarski(k2_zfmisc_1(k3_xboole_0('#skF_3',A_1230),'#skF_4'),k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_101760,c_55243])).

tff(c_102490,plain,(
    ! [A_1230] :
      ( r1_tarski(k3_xboole_0('#skF_3',A_1230),'#skF_1')
      | k1_xboole_0 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_102487,c_20])).

tff(c_102607,plain,(
    ! [A_1232] : r1_tarski(k3_xboole_0('#skF_3',A_1232),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_71736,c_102490])).

tff(c_102650,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_102607])).

tff(c_102661,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54416,c_102650])).

tff(c_102662,plain,(
    '#skF_2' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_102677,plain,(
    ! [A_1234,B_1235] : r1_tarski(k3_xboole_0(A_1234,B_1235),A_1234) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_102680,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_102677])).

tff(c_102663,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_102681,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k2_zfmisc_1('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102663,c_38])).

tff(c_102822,plain,(
    ! [A_1251,C_1252,B_1253] :
      ( r1_tarski(k2_zfmisc_1(A_1251,C_1252),k2_zfmisc_1(B_1253,C_1252))
      | ~ r1_tarski(A_1251,B_1253) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_102831,plain,(
    ! [A_1251] :
      ( r1_tarski(k2_zfmisc_1(A_1251,'#skF_2'),k2_zfmisc_1('#skF_1','#skF_4'))
      | ~ r1_tarski(A_1251,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102681,c_102822])).

tff(c_103486,plain,(
    ! [A_1275,B_1276,C_1277] :
      ( ~ r1_tarski(k2_zfmisc_1(A_1275,B_1276),k2_zfmisc_1(A_1275,C_1277))
      | r1_tarski(B_1276,C_1277)
      | k1_xboole_0 = A_1275 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_103496,plain,
    ( r1_tarski('#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_102831,c_103486])).

tff(c_103517,plain,
    ( r1_tarski('#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102680,c_103496])).

tff(c_103518,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_103517])).

tff(c_102756,plain,(
    ! [A_1247,B_1248] :
      ( r2_xboole_0(A_1247,B_1248)
      | B_1248 = A_1247
      | ~ r1_tarski(A_1247,B_1248) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_102767,plain,(
    ! [B_1248,A_1247] :
      ( ~ r1_tarski(B_1248,A_1247)
      | B_1248 = A_1247
      | ~ r1_tarski(A_1247,B_1248) ) ),
    inference(resolution,[status(thm)],[c_102756,c_16])).

tff(c_103527,plain,
    ( '#skF_2' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_103518,c_102767])).

tff(c_103533,plain,(
    ~ r1_tarski('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_102662,c_103527])).

tff(c_24,plain,(
    ! [A_16,C_18,B_17] :
      ( r1_tarski(k2_zfmisc_1(A_16,C_18),k2_zfmisc_1(B_17,C_18))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_103510,plain,(
    ! [B_1276] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1',B_1276),k2_zfmisc_1('#skF_1','#skF_4'))
      | r1_tarski(B_1276,'#skF_2')
      | k1_xboole_0 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102681,c_103486])).

tff(c_103735,plain,(
    ! [B_1283] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1',B_1283),k2_zfmisc_1('#skF_1','#skF_4'))
      | r1_tarski(B_1283,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_103510])).

tff(c_103750,plain,
    ( r1_tarski('#skF_4','#skF_2')
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_103735])).

tff(c_103765,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102680,c_103750])).

tff(c_103767,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103533,c_103765])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:14:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 27.50/17.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.64/17.13  
% 27.64/17.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.64/17.13  %$ r2_xboole_0 > r1_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 27.64/17.13  
% 27.64/17.13  %Foreground sorts:
% 27.64/17.13  
% 27.64/17.13  
% 27.64/17.13  %Background operators:
% 27.64/17.13  
% 27.64/17.13  
% 27.64/17.13  %Foreground operators:
% 27.64/17.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 27.64/17.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 27.64/17.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 27.64/17.13  tff('#skF_2', type, '#skF_2': $i).
% 27.64/17.13  tff('#skF_3', type, '#skF_3': $i).
% 27.64/17.13  tff('#skF_1', type, '#skF_1': $i).
% 27.64/17.13  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 27.64/17.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 27.64/17.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 27.64/17.13  tff('#skF_4', type, '#skF_4': $i).
% 27.64/17.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 27.64/17.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 27.64/17.13  
% 27.64/17.16  tff(f_81, negated_conjecture, ~(![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 27.64/17.16  tff(f_64, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 27.64/17.16  tff(f_58, axiom, (![A, B, C]: ~((~(A = k1_xboole_0) & (r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(C, A)) | r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(A, C)))) & ~r1_tarski(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 27.64/17.16  tff(f_36, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 27.64/17.16  tff(f_38, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 27.64/17.16  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 27.64/17.16  tff(f_70, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 27.64/17.16  tff(f_42, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 27.64/17.16  tff(f_68, axiom, (![A, B, C]: ((k2_zfmisc_1(k3_xboole_0(A, B), C) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t122_zfmisc_1)).
% 27.64/17.16  tff(f_34, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 27.64/17.16  tff(f_47, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_xboole_1)).
% 27.64/17.16  tff(c_32, plain, ('#skF_2'!='#skF_4' | '#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_81])).
% 27.64/17.16  tff(c_40, plain, ('#skF_3'!='#skF_1'), inference(splitLeft, [status(thm)], [c_32])).
% 27.64/17.16  tff(c_34, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_81])).
% 27.64/17.16  tff(c_36, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_81])).
% 27.64/17.16  tff(c_38, plain, (k2_zfmisc_1('#skF_3', '#skF_4')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 27.64/17.16  tff(c_274, plain, (![A_49, C_50, B_51]: (r1_tarski(k2_zfmisc_1(A_49, C_50), k2_zfmisc_1(B_51, C_50)) | ~r1_tarski(A_49, B_51))), inference(cnfTransformation, [status(thm)], [f_64])).
% 27.64/17.16  tff(c_285, plain, (![A_49]: (r1_tarski(k2_zfmisc_1(A_49, '#skF_4'), k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski(A_49, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_274])).
% 27.64/17.16  tff(c_945, plain, (![A_72, B_73, C_74]: (~r1_tarski(k2_zfmisc_1(A_72, B_73), k2_zfmisc_1(A_72, C_74)) | r1_tarski(B_73, C_74) | k1_xboole_0=A_72)), inference(cnfTransformation, [status(thm)], [f_58])).
% 27.64/17.16  tff(c_949, plain, (r1_tarski('#skF_4', '#skF_2') | k1_xboole_0='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_285, c_945])).
% 27.64/17.16  tff(c_969, plain, (r1_tarski('#skF_4', '#skF_2') | ~r1_tarski('#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_36, c_949])).
% 27.64/17.16  tff(c_976, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_969])).
% 27.64/17.16  tff(c_493, plain, (![C_58, A_59, B_60]: (r1_tarski(k2_zfmisc_1(C_58, A_59), k2_zfmisc_1(C_58, B_60)) | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_64])).
% 27.64/17.16  tff(c_501, plain, (![B_60]: (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', B_60)) | ~r1_tarski('#skF_4', B_60))), inference(superposition, [status(thm), theory('equality')], [c_38, c_493])).
% 27.64/17.16  tff(c_1126, plain, (![B_78, A_79, C_80]: (~r1_tarski(k2_zfmisc_1(B_78, A_79), k2_zfmisc_1(C_80, A_79)) | r1_tarski(B_78, C_80) | k1_xboole_0=A_79)), inference(cnfTransformation, [status(thm)], [f_58])).
% 27.64/17.16  tff(c_1130, plain, (r1_tarski('#skF_1', '#skF_3') | k1_xboole_0='#skF_2' | ~r1_tarski('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_501, c_1126])).
% 27.64/17.16  tff(c_1154, plain, (~r1_tarski('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_34, c_976, c_1130])).
% 27.64/17.16  tff(c_10, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 27.64/17.16  tff(c_50, plain, (![A_28, B_29]: (r1_tarski(k3_xboole_0(A_28, B_29), A_28))), inference(cnfTransformation, [status(thm)], [f_38])).
% 27.64/17.16  tff(c_53, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_10, c_50])).
% 27.64/17.16  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 27.64/17.16  tff(c_504, plain, (![A_59]: (r1_tarski(k2_zfmisc_1('#skF_3', A_59), k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski(A_59, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_493])).
% 27.64/17.16  tff(c_1134, plain, (r1_tarski('#skF_3', '#skF_1') | k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_504, c_1126])).
% 27.64/17.16  tff(c_1157, plain, (r1_tarski('#skF_3', '#skF_1') | ~r1_tarski('#skF_2', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_34, c_1134])).
% 27.64/17.16  tff(c_1164, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_1157])).
% 27.64/17.16  tff(c_30, plain, (![A_22, C_24, B_23, D_25]: (k3_xboole_0(k2_zfmisc_1(A_22, C_24), k2_zfmisc_1(B_23, D_25))=k2_zfmisc_1(k3_xboole_0(A_22, B_23), k3_xboole_0(C_24, D_25)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 27.64/17.16  tff(c_1658, plain, (![A_100, C_101, B_102, D_103]: (k3_xboole_0(k2_zfmisc_1(A_100, C_101), k2_zfmisc_1(B_102, D_103))=k2_zfmisc_1(k3_xboole_0(A_100, B_102), k3_xboole_0(C_101, D_103)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 27.64/17.16  tff(c_1751, plain, (![A_100, C_101]: (k3_xboole_0(k2_zfmisc_1(A_100, C_101), k2_zfmisc_1('#skF_1', '#skF_2'))=k2_zfmisc_1(k3_xboole_0(A_100, '#skF_3'), k3_xboole_0(C_101, '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1658])).
% 27.64/17.16  tff(c_26582, plain, (![A_374, C_375]: (k2_zfmisc_1(k3_xboole_0(A_374, '#skF_3'), k3_xboole_0(C_375, '#skF_4'))=k2_zfmisc_1(k3_xboole_0(A_374, '#skF_1'), k3_xboole_0(C_375, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1751])).
% 27.64/17.16  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 27.64/17.16  tff(c_1937, plain, (![A_109, B_110, C_111, D_112]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_109, B_110), k3_xboole_0(C_111, D_112)), k2_zfmisc_1(A_109, C_111)))), inference(superposition, [status(thm), theory('equality')], [c_1658, c_12])).
% 27.64/17.16  tff(c_2020, plain, (![A_109, B_110, A_1, B_2]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_109, B_110), k3_xboole_0(A_1, B_2)), k2_zfmisc_1(A_109, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1937])).
% 27.64/17.16  tff(c_26853, plain, (![A_376, C_377]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_376, '#skF_1'), k3_xboole_0(C_377, '#skF_2')), k2_zfmisc_1(A_376, '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_26582, c_2020])).
% 27.64/17.16  tff(c_26979, plain, (![C_378]: (r1_tarski(k2_zfmisc_1('#skF_1', k3_xboole_0(C_378, '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_10, c_26853])).
% 27.64/17.16  tff(c_18, plain, (![A_13, B_14, C_15]: (~r1_tarski(k2_zfmisc_1(A_13, B_14), k2_zfmisc_1(A_13, C_15)) | r1_tarski(B_14, C_15) | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_58])).
% 27.64/17.16  tff(c_26982, plain, (![C_378]: (r1_tarski(k3_xboole_0(C_378, '#skF_2'), '#skF_4') | k1_xboole_0='#skF_1')), inference(resolution, [status(thm)], [c_26979, c_18])).
% 27.64/17.16  tff(c_27039, plain, (![C_379]: (r1_tarski(k3_xboole_0(C_379, '#skF_2'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_36, c_26982])).
% 27.64/17.16  tff(c_27072, plain, (r1_tarski('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10, c_27039])).
% 27.64/17.16  tff(c_27078, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1164, c_27072])).
% 27.64/17.16  tff(c_27080, plain, (r1_tarski('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_1157])).
% 27.64/17.16  tff(c_14, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 27.64/17.16  tff(c_27115, plain, (k3_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(resolution, [status(thm)], [c_27080, c_14])).
% 27.64/17.16  tff(c_27228, plain, (k3_xboole_0('#skF_4', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_2, c_27115])).
% 27.64/17.16  tff(c_27079, plain, (r1_tarski('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_1157])).
% 27.64/17.16  tff(c_27108, plain, (k3_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_27079, c_14])).
% 27.64/17.16  tff(c_845, plain, (![C_68, A_69, B_70]: (k3_xboole_0(k2_zfmisc_1(C_68, A_69), k2_zfmisc_1(C_68, B_70))=k2_zfmisc_1(C_68, k3_xboole_0(A_69, B_70)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 27.64/17.16  tff(c_29077, plain, (![C_427, B_428, A_429]: (k3_xboole_0(k2_zfmisc_1(C_427, B_428), k2_zfmisc_1(C_427, A_429))=k2_zfmisc_1(C_427, k3_xboole_0(A_429, B_428)))), inference(superposition, [status(thm), theory('equality')], [c_845, c_2])).
% 27.64/17.16  tff(c_39751, plain, (![B_543]: (k3_xboole_0(k2_zfmisc_1('#skF_3', B_543), k2_zfmisc_1('#skF_1', '#skF_2'))=k2_zfmisc_1('#skF_3', k3_xboole_0('#skF_4', B_543)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_29077])).
% 27.64/17.16  tff(c_39802, plain, (![B_543]: (k2_zfmisc_1(k3_xboole_0('#skF_3', '#skF_1'), k3_xboole_0(B_543, '#skF_2'))=k2_zfmisc_1('#skF_3', k3_xboole_0('#skF_4', B_543)))), inference(superposition, [status(thm), theory('equality')], [c_39751, c_30])).
% 27.64/17.16  tff(c_53750, plain, (![B_702]: (k2_zfmisc_1('#skF_3', k3_xboole_0(B_702, '#skF_2'))=k2_zfmisc_1('#skF_3', k3_xboole_0('#skF_4', B_702)))), inference(demodulation, [status(thm), theory('equality')], [c_27108, c_39802])).
% 27.64/17.16  tff(c_54149, plain, (k2_zfmisc_1('#skF_3', k3_xboole_0('#skF_4', '#skF_4'))=k2_zfmisc_1('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_27228, c_53750])).
% 27.64/17.16  tff(c_54238, plain, (k2_zfmisc_1('#skF_3', '#skF_2')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_10, c_54149])).
% 27.64/17.16  tff(c_22, plain, (![C_18, A_16, B_17]: (r1_tarski(k2_zfmisc_1(C_18, A_16), k2_zfmisc_1(C_18, B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 27.64/17.16  tff(c_959, plain, (![C_74]: (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', C_74)) | r1_tarski('#skF_4', C_74) | k1_xboole_0='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_38, c_945])).
% 27.64/17.16  tff(c_29246, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_959])).
% 27.64/17.16  tff(c_29249, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_29246, c_34])).
% 27.64/17.16  tff(c_35540, plain, (![B_505]: (k3_xboole_0(k2_zfmisc_1('#skF_3', B_505), k2_zfmisc_1('#skF_1', '#skF_2'))=k2_zfmisc_1('#skF_3', k3_xboole_0('#skF_4', B_505)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_29077])).
% 27.64/17.16  tff(c_35627, plain, (![B_505]: (k2_zfmisc_1(k3_xboole_0('#skF_3', '#skF_1'), k3_xboole_0(B_505, '#skF_2'))=k2_zfmisc_1('#skF_3', k3_xboole_0('#skF_4', B_505)))), inference(superposition, [status(thm), theory('equality')], [c_35540, c_30])).
% 27.64/17.16  tff(c_35754, plain, (![B_506]: (k2_zfmisc_1('#skF_3', k3_xboole_0(B_506, '#skF_2'))=k2_zfmisc_1('#skF_3', k3_xboole_0('#skF_4', B_506)))), inference(demodulation, [status(thm), theory('equality')], [c_27108, c_35627])).
% 27.64/17.16  tff(c_35983, plain, (k2_zfmisc_1('#skF_3', k3_xboole_0('#skF_4', '#skF_4'))=k2_zfmisc_1('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_27228, c_35754])).
% 27.64/17.16  tff(c_36041, plain, (k2_zfmisc_1('#skF_3', '#skF_2')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_10, c_35983])).
% 27.64/17.16  tff(c_20, plain, (![B_14, A_13, C_15]: (~r1_tarski(k2_zfmisc_1(B_14, A_13), k2_zfmisc_1(C_15, A_13)) | r1_tarski(B_14, C_15) | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_58])).
% 27.64/17.16  tff(c_36490, plain, (![B_510, A_511, C_512]: (~r1_tarski(k2_zfmisc_1(B_510, A_511), k2_zfmisc_1(C_512, A_511)) | r1_tarski(B_510, C_512) | A_511='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_29246, c_20])).
% 27.64/17.16  tff(c_36496, plain, (![B_510]: (~r1_tarski(k2_zfmisc_1(B_510, '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')) | r1_tarski(B_510, '#skF_3') | '#skF_2'='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36041, c_36490])).
% 27.64/17.16  tff(c_37314, plain, (![B_524]: (~r1_tarski(k2_zfmisc_1(B_524, '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')) | r1_tarski(B_524, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_29249, c_36496])).
% 27.64/17.16  tff(c_37351, plain, (r1_tarski('#skF_1', '#skF_3') | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_22, c_37314])).
% 27.64/17.16  tff(c_37375, plain, (r1_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_53, c_37351])).
% 27.64/17.16  tff(c_37377, plain, $false, inference(negUnitSimplification, [status(thm)], [c_976, c_37375])).
% 27.64/17.16  tff(c_37378, plain, (![C_74]: (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', C_74)) | r1_tarski('#skF_4', C_74))), inference(splitRight, [status(thm)], [c_959])).
% 27.64/17.16  tff(c_54307, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')) | r1_tarski('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_54238, c_37378])).
% 27.64/17.16  tff(c_54397, plain, (r1_tarski('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_53, c_54307])).
% 27.64/17.16  tff(c_54399, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1154, c_54397])).
% 27.64/17.16  tff(c_54401, plain, (r1_tarski('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_969])).
% 27.64/17.16  tff(c_128, plain, (![A_41, B_42]: (r2_xboole_0(A_41, B_42) | B_42=A_41 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_34])).
% 27.64/17.16  tff(c_16, plain, (![B_12, A_11]: (~r2_xboole_0(B_12, A_11) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 27.64/17.16  tff(c_139, plain, (![B_42, A_41]: (~r1_tarski(B_42, A_41) | B_42=A_41 | ~r1_tarski(A_41, B_42))), inference(resolution, [status(thm)], [c_128, c_16])).
% 27.64/17.16  tff(c_54410, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_54401, c_139])).
% 27.64/17.16  tff(c_54416, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_40, c_54410])).
% 27.64/17.16  tff(c_54418, plain, (![B_703, A_704, C_705]: (~r1_tarski(k2_zfmisc_1(B_703, A_704), k2_zfmisc_1(C_705, A_704)) | r1_tarski(B_703, C_705) | k1_xboole_0=A_704)), inference(cnfTransformation, [status(thm)], [f_58])).
% 27.64/17.16  tff(c_54422, plain, (r1_tarski('#skF_3', '#skF_1') | k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_504, c_54418])).
% 27.64/17.16  tff(c_54442, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_34, c_54416, c_54422])).
% 27.64/17.16  tff(c_54435, plain, (![B_703]: (~r1_tarski(k2_zfmisc_1(B_703, '#skF_4'), k2_zfmisc_1('#skF_1', '#skF_2')) | r1_tarski(B_703, '#skF_3') | k1_xboole_0='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_38, c_54418])).
% 27.64/17.16  tff(c_56320, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_54435])).
% 27.64/17.16  tff(c_56324, plain, ('#skF_1'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56320, c_36])).
% 27.64/17.16  tff(c_54400, plain, (r1_tarski('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_969])).
% 27.64/17.16  tff(c_54408, plain, (k3_xboole_0('#skF_4', '#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_54400, c_14])).
% 27.64/17.16  tff(c_61, plain, (![B_35, A_36]: (k3_xboole_0(B_35, A_36)=k3_xboole_0(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_27])).
% 27.64/17.16  tff(c_76, plain, (![B_35, A_36]: (r1_tarski(k3_xboole_0(B_35, A_36), A_36))), inference(superposition, [status(thm), theory('equality')], [c_61, c_12])).
% 27.64/17.16  tff(c_114, plain, (![A_39, B_40]: (k3_xboole_0(A_39, B_40)=A_39 | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_42])).
% 27.64/17.16  tff(c_207, plain, (![B_47, A_48]: (k3_xboole_0(k3_xboole_0(B_47, A_48), A_48)=k3_xboole_0(B_47, A_48))), inference(resolution, [status(thm)], [c_76, c_114])).
% 27.64/17.16  tff(c_255, plain, (![A_1, B_2]: (k3_xboole_0(k3_xboole_0(A_1, B_2), A_1)=k3_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_207])).
% 27.64/17.16  tff(c_54455, plain, (k3_xboole_0('#skF_2', '#skF_4')=k3_xboole_0('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_54408, c_255])).
% 27.64/17.16  tff(c_54486, plain, (k3_xboole_0('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_54455])).
% 27.64/17.16  tff(c_145, plain, (![A_43, B_44]: (k3_xboole_0(k3_xboole_0(A_43, B_44), A_43)=k3_xboole_0(A_43, B_44))), inference(resolution, [status(thm)], [c_12, c_114])).
% 27.64/17.16  tff(c_179, plain, (![A_1, B_2]: (k3_xboole_0(k3_xboole_0(A_1, B_2), B_2)=k3_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_145])).
% 27.64/17.16  tff(c_906, plain, (![A_69]: (k3_xboole_0(k2_zfmisc_1('#skF_3', A_69), k2_zfmisc_1('#skF_1', '#skF_2'))=k2_zfmisc_1('#skF_3', k3_xboole_0(A_69, '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_38, c_845])).
% 27.64/17.16  tff(c_54417, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_54401, c_14])).
% 27.64/17.16  tff(c_56377, plain, (![A_755]: (k3_xboole_0(k2_zfmisc_1('#skF_3', A_755), k2_zfmisc_1('#skF_1', '#skF_2'))=k2_zfmisc_1('#skF_3', k3_xboole_0(A_755, '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_38, c_845])).
% 27.64/17.16  tff(c_124, plain, (![B_35, A_36]: (k3_xboole_0(k3_xboole_0(B_35, A_36), A_36)=k3_xboole_0(B_35, A_36))), inference(resolution, [status(thm)], [c_76, c_114])).
% 27.64/17.16  tff(c_56448, plain, (![A_755]: (k3_xboole_0(k2_zfmisc_1('#skF_3', k3_xboole_0(A_755, '#skF_4')), k2_zfmisc_1('#skF_1', '#skF_2'))=k3_xboole_0(k2_zfmisc_1('#skF_3', A_755), k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_56377, c_124])).
% 27.64/17.16  tff(c_70331, plain, (![A_914]: (k2_zfmisc_1('#skF_3', k3_xboole_0('#skF_4', A_914))=k2_zfmisc_1('#skF_1', k3_xboole_0('#skF_2', A_914)))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_906, c_54417, c_30, c_2, c_56448])).
% 27.64/17.16  tff(c_70473, plain, (k2_zfmisc_1('#skF_1', k3_xboole_0('#skF_2', '#skF_4'))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10, c_70331])).
% 27.64/17.16  tff(c_70489, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k2_zfmisc_1('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_54486, c_70473])).
% 27.64/17.16  tff(c_55065, plain, (![C_717, A_718, B_719]: (r1_tarski(k2_zfmisc_1(C_717, k3_xboole_0(A_718, B_719)), k2_zfmisc_1(C_717, A_718)))), inference(superposition, [status(thm), theory('equality')], [c_845, c_12])).
% 27.64/17.16  tff(c_55124, plain, (![C_717, A_1, B_2]: (r1_tarski(k2_zfmisc_1(C_717, k3_xboole_0(A_1, B_2)), k2_zfmisc_1(C_717, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_55065])).
% 27.64/17.16  tff(c_70540, plain, (![A_1]: (r1_tarski(k2_zfmisc_1('#skF_1', k3_xboole_0(A_1, '#skF_2')), k2_zfmisc_1('#skF_1', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_70489, c_55124])).
% 27.64/17.16  tff(c_71564, plain, (![A_924, B_925, C_926]: (~r1_tarski(k2_zfmisc_1(A_924, B_925), k2_zfmisc_1(A_924, C_926)) | r1_tarski(B_925, C_926) | A_924='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56320, c_18])).
% 27.64/17.16  tff(c_71567, plain, (![A_1]: (r1_tarski(k3_xboole_0(A_1, '#skF_2'), '#skF_4') | '#skF_1'='#skF_4')), inference(resolution, [status(thm)], [c_70540, c_71564])).
% 27.64/17.16  tff(c_71692, plain, (![A_927]: (r1_tarski(k3_xboole_0(A_927, '#skF_2'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_56324, c_71567])).
% 27.64/17.16  tff(c_71727, plain, (r1_tarski('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10, c_71692])).
% 27.64/17.16  tff(c_71734, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54442, c_71727])).
% 27.64/17.16  tff(c_71736, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_54435])).
% 27.64/17.16  tff(c_54962, plain, (![A_713, C_714, B_715, D_716]: (k3_xboole_0(k2_zfmisc_1(A_713, C_714), k2_zfmisc_1(B_715, D_716))=k2_zfmisc_1(k3_xboole_0(A_713, B_715), k3_xboole_0(C_714, D_716)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 27.64/17.16  tff(c_93184, plain, (![B_1134, D_1135, A_1136, C_1137]: (k3_xboole_0(k2_zfmisc_1(B_1134, D_1135), k2_zfmisc_1(A_1136, C_1137))=k2_zfmisc_1(k3_xboole_0(A_1136, B_1134), k3_xboole_0(C_1137, D_1135)))), inference(superposition, [status(thm), theory('equality')], [c_54962, c_2])).
% 27.64/17.16  tff(c_54694, plain, (![A_707, C_708, B_709]: (k3_xboole_0(k2_zfmisc_1(A_707, C_708), k2_zfmisc_1(B_709, C_708))=k2_zfmisc_1(k3_xboole_0(A_707, B_709), C_708))), inference(cnfTransformation, [status(thm)], [f_68])).
% 27.64/17.16  tff(c_54760, plain, (![B_709]: (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1(B_709, '#skF_4'))=k2_zfmisc_1(k3_xboole_0('#skF_3', B_709), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_54694])).
% 27.64/17.16  tff(c_93238, plain, (![A_1136]: (k2_zfmisc_1(k3_xboole_0(A_1136, '#skF_1'), k3_xboole_0('#skF_4', '#skF_2'))=k2_zfmisc_1(k3_xboole_0('#skF_3', A_1136), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_93184, c_54760])).
% 27.64/17.16  tff(c_101760, plain, (![A_1229]: (k2_zfmisc_1(k3_xboole_0(A_1229, '#skF_1'), '#skF_4')=k2_zfmisc_1(k3_xboole_0('#skF_3', A_1229), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54408, c_93238])).
% 27.64/17.16  tff(c_55184, plain, (![A_722, B_723, C_724]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_722, B_723), C_724), k2_zfmisc_1(A_722, C_724)))), inference(superposition, [status(thm), theory('equality')], [c_54694, c_12])).
% 27.64/17.16  tff(c_55243, plain, (![A_1, B_2, C_724]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_1, B_2), C_724), k2_zfmisc_1(B_2, C_724)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_55184])).
% 27.64/17.16  tff(c_102487, plain, (![A_1230]: (r1_tarski(k2_zfmisc_1(k3_xboole_0('#skF_3', A_1230), '#skF_4'), k2_zfmisc_1('#skF_1', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_101760, c_55243])).
% 27.64/17.16  tff(c_102490, plain, (![A_1230]: (r1_tarski(k3_xboole_0('#skF_3', A_1230), '#skF_1') | k1_xboole_0='#skF_4')), inference(resolution, [status(thm)], [c_102487, c_20])).
% 27.64/17.16  tff(c_102607, plain, (![A_1232]: (r1_tarski(k3_xboole_0('#skF_3', A_1232), '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_71736, c_102490])).
% 27.64/17.16  tff(c_102650, plain, (r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_10, c_102607])).
% 27.64/17.16  tff(c_102661, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54416, c_102650])).
% 27.64/17.16  tff(c_102662, plain, ('#skF_2'!='#skF_4'), inference(splitRight, [status(thm)], [c_32])).
% 27.64/17.16  tff(c_102677, plain, (![A_1234, B_1235]: (r1_tarski(k3_xboole_0(A_1234, B_1235), A_1234))), inference(cnfTransformation, [status(thm)], [f_38])).
% 27.64/17.16  tff(c_102680, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_10, c_102677])).
% 27.64/17.16  tff(c_102663, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_32])).
% 27.64/17.16  tff(c_102681, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k2_zfmisc_1('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_102663, c_38])).
% 27.64/17.16  tff(c_102822, plain, (![A_1251, C_1252, B_1253]: (r1_tarski(k2_zfmisc_1(A_1251, C_1252), k2_zfmisc_1(B_1253, C_1252)) | ~r1_tarski(A_1251, B_1253))), inference(cnfTransformation, [status(thm)], [f_64])).
% 27.64/17.16  tff(c_102831, plain, (![A_1251]: (r1_tarski(k2_zfmisc_1(A_1251, '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_4')) | ~r1_tarski(A_1251, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_102681, c_102822])).
% 27.64/17.16  tff(c_103486, plain, (![A_1275, B_1276, C_1277]: (~r1_tarski(k2_zfmisc_1(A_1275, B_1276), k2_zfmisc_1(A_1275, C_1277)) | r1_tarski(B_1276, C_1277) | k1_xboole_0=A_1275)), inference(cnfTransformation, [status(thm)], [f_58])).
% 27.64/17.16  tff(c_103496, plain, (r1_tarski('#skF_2', '#skF_4') | k1_xboole_0='#skF_1' | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_102831, c_103486])).
% 27.64/17.16  tff(c_103517, plain, (r1_tarski('#skF_2', '#skF_4') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_102680, c_103496])).
% 27.64/17.16  tff(c_103518, plain, (r1_tarski('#skF_2', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_36, c_103517])).
% 27.64/17.16  tff(c_102756, plain, (![A_1247, B_1248]: (r2_xboole_0(A_1247, B_1248) | B_1248=A_1247 | ~r1_tarski(A_1247, B_1248))), inference(cnfTransformation, [status(thm)], [f_34])).
% 27.64/17.16  tff(c_102767, plain, (![B_1248, A_1247]: (~r1_tarski(B_1248, A_1247) | B_1248=A_1247 | ~r1_tarski(A_1247, B_1248))), inference(resolution, [status(thm)], [c_102756, c_16])).
% 27.64/17.16  tff(c_103527, plain, ('#skF_2'='#skF_4' | ~r1_tarski('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_103518, c_102767])).
% 27.64/17.16  tff(c_103533, plain, (~r1_tarski('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_102662, c_103527])).
% 27.64/17.16  tff(c_24, plain, (![A_16, C_18, B_17]: (r1_tarski(k2_zfmisc_1(A_16, C_18), k2_zfmisc_1(B_17, C_18)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 27.64/17.16  tff(c_103510, plain, (![B_1276]: (~r1_tarski(k2_zfmisc_1('#skF_1', B_1276), k2_zfmisc_1('#skF_1', '#skF_4')) | r1_tarski(B_1276, '#skF_2') | k1_xboole_0='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_102681, c_103486])).
% 27.64/17.16  tff(c_103735, plain, (![B_1283]: (~r1_tarski(k2_zfmisc_1('#skF_1', B_1283), k2_zfmisc_1('#skF_1', '#skF_4')) | r1_tarski(B_1283, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_36, c_103510])).
% 27.64/17.16  tff(c_103750, plain, (r1_tarski('#skF_4', '#skF_2') | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_24, c_103735])).
% 27.64/17.16  tff(c_103765, plain, (r1_tarski('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_102680, c_103750])).
% 27.64/17.16  tff(c_103767, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103533, c_103765])).
% 27.64/17.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.64/17.16  
% 27.64/17.16  Inference rules
% 27.64/17.16  ----------------------
% 27.64/17.16  #Ref     : 0
% 27.64/17.16  #Sup     : 26198
% 27.64/17.16  #Fact    : 0
% 27.64/17.16  #Define  : 0
% 27.64/17.16  #Split   : 17
% 27.64/17.16  #Chain   : 0
% 27.64/17.16  #Close   : 0
% 27.64/17.16  
% 27.64/17.16  Ordering : KBO
% 27.64/17.16  
% 27.64/17.16  Simplification rules
% 27.64/17.16  ----------------------
% 27.64/17.16  #Subsume      : 1810
% 27.64/17.16  #Demod        : 22242
% 27.64/17.16  #Tautology    : 11161
% 27.64/17.16  #SimpNegUnit  : 240
% 27.64/17.16  #BackRed      : 176
% 27.64/17.16  
% 27.64/17.16  #Partial instantiations: 0
% 27.64/17.16  #Strategies tried      : 1
% 27.64/17.16  
% 27.64/17.16  Timing (in seconds)
% 27.64/17.16  ----------------------
% 27.64/17.16  Preprocessing        : 0.48
% 27.64/17.16  Parsing              : 0.25
% 27.64/17.16  CNF conversion       : 0.03
% 27.64/17.16  Main loop            : 15.75
% 27.64/17.16  Inferencing          : 2.23
% 27.64/17.16  Reduction            : 9.42
% 27.64/17.16  Demodulation         : 8.45
% 27.64/17.16  BG Simplification    : 0.37
% 27.64/17.16  Subsumption          : 2.89
% 27.64/17.16  Abstraction          : 0.51
% 27.64/17.16  MUC search           : 0.00
% 27.64/17.16  Cooper               : 0.00
% 27.64/17.16  Total                : 16.29
% 27.64/17.16  Index Insertion      : 0.00
% 27.64/17.16  Index Deletion       : 0.00
% 27.64/17.16  Index Matching       : 0.00
% 27.64/17.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
