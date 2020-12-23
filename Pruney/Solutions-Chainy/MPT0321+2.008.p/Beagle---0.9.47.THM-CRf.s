%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:14 EST 2020

% Result     : Theorem 25.33s
% Output     : CNFRefutation 25.56s
% Verified   : 
% Statistics : Number of formulae       :  246 (1914 expanded)
%              Number of leaves         :   23 ( 639 expanded)
%              Depth                    :   22
%              Number of atoms          :  330 (3439 expanded)
%              Number of equality atoms :  177 (2241 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_64,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
          | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
        & ~ r1_tarski(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_30,plain,
    ( '#skF_2' != '#skF_4'
    | '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_39,plain,(
    '#skF_3' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_26,plain,(
    ! [C_20,A_18,B_19] : k2_xboole_0(k2_zfmisc_1(C_20,A_18),k2_zfmisc_1(C_20,B_19)) = k2_zfmisc_1(C_20,k2_xboole_0(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_36,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_874,plain,(
    ! [A_69,C_70,B_71] : k2_xboole_0(k2_zfmisc_1(A_69,C_70),k2_zfmisc_1(B_71,C_70)) = k2_zfmisc_1(k2_xboole_0(A_69,B_71),C_70) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_76676,plain,(
    ! [A_744] : k2_xboole_0(k2_zfmisc_1(A_744,'#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) = k2_zfmisc_1(k2_xboole_0(A_744,'#skF_3'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_874])).

tff(c_76761,plain,(
    k2_zfmisc_1(k2_xboole_0('#skF_1','#skF_3'),'#skF_4') = k2_zfmisc_1('#skF_1',k2_xboole_0('#skF_4','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_76676])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_166,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = A_40
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_224,plain,(
    ! [A_44,B_45] : k3_xboole_0(A_44,k2_xboole_0(A_44,B_45)) = A_44 ),
    inference(resolution,[status(thm)],[c_18,c_166])).

tff(c_248,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,k2_xboole_0(A_1,B_2)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_224])).

tff(c_185,plain,(
    ! [A_13,B_14] : k3_xboole_0(A_13,k2_xboole_0(A_13,B_14)) = A_13 ),
    inference(resolution,[status(thm)],[c_18,c_166])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_111,plain,(
    ! [B_36,A_37] : k3_xboole_0(B_36,A_37) = k3_xboole_0(A_37,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_135,plain,(
    ! [B_36,A_37] : k2_xboole_0(B_36,k3_xboole_0(A_37,B_36)) = B_36 ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_14])).

tff(c_328,plain,(
    ! [B_50,A_51] : k3_xboole_0(B_50,k2_xboole_0(A_51,B_50)) = B_50 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_224])).

tff(c_61665,plain,(
    ! [A_562,B_563] : k3_xboole_0(k3_xboole_0(A_562,B_563),B_563) = k3_xboole_0(A_562,B_563) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_328])).

tff(c_62086,plain,(
    ! [B_570,A_571] : k3_xboole_0(B_570,k3_xboole_0(A_571,B_570)) = k3_xboole_0(A_571,B_570) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_61665])).

tff(c_62134,plain,(
    ! [A_13,B_14] : k3_xboole_0(k2_xboole_0(A_13,B_14),A_13) = k3_xboole_0(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_62086])).

tff(c_62159,plain,(
    ! [A_13,B_14] : k3_xboole_0(k2_xboole_0(A_13,B_14),A_13) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_62134])).

tff(c_28,plain,(
    ! [A_21,C_23,B_22,D_24] : k3_xboole_0(k2_zfmisc_1(A_21,C_23),k2_zfmisc_1(B_22,D_24)) = k2_zfmisc_1(k3_xboole_0(A_21,B_22),k3_xboole_0(C_23,D_24)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_281,plain,(
    ! [B_48,A_49] : k2_xboole_0(B_48,k3_xboole_0(A_49,B_48)) = B_48 ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_14])).

tff(c_605,plain,(
    ! [A_63,B_64] : k2_xboole_0(k2_xboole_0(A_63,B_64),A_63) = k2_xboole_0(A_63,B_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_281])).

tff(c_656,plain,(
    ! [B_2,A_1] : k2_xboole_0(k2_xboole_0(B_2,A_1),A_1) = k2_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_605])).

tff(c_82130,plain,(
    ! [A_822] : k3_xboole_0(k2_zfmisc_1(A_822,'#skF_4'),k2_zfmisc_1(k2_xboole_0(A_822,'#skF_3'),'#skF_4')) = k2_zfmisc_1(A_822,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_76676,c_185])).

tff(c_82223,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_1',k2_xboole_0('#skF_4','#skF_2')),k2_zfmisc_1(k2_xboole_0(k2_xboole_0('#skF_1','#skF_3'),'#skF_3'),'#skF_4')) = k2_zfmisc_1(k2_xboole_0('#skF_1','#skF_3'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_76761,c_82130])).

tff(c_82316,plain,(
    k2_zfmisc_1('#skF_1',k2_xboole_0('#skF_4','#skF_2')) = k2_zfmisc_1('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76761,c_248,c_62159,c_28,c_656,c_82223])).

tff(c_61757,plain,(
    ! [C_564,A_565,B_566] : k2_xboole_0(k2_zfmisc_1(C_564,A_565),k2_zfmisc_1(C_564,B_566)) = k2_zfmisc_1(C_564,k2_xboole_0(A_565,B_566)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_54,plain,(
    ! [B_30,A_31] : k2_xboole_0(B_30,A_31) = k2_xboole_0(A_31,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_69,plain,(
    ! [A_31,B_30] : r1_tarski(A_31,k2_xboole_0(B_30,A_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_18])).

tff(c_61801,plain,(
    ! [C_564,B_566,A_565] : r1_tarski(k2_zfmisc_1(C_564,B_566),k2_zfmisc_1(C_564,k2_xboole_0(A_565,B_566))) ),
    inference(superposition,[status(thm),theory(equality)],[c_61757,c_69])).

tff(c_82370,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_82316,c_61801])).

tff(c_62420,plain,(
    ! [B_576,A_577,C_578] :
      ( ~ r1_tarski(k2_zfmisc_1(B_576,A_577),k2_zfmisc_1(C_578,A_577))
      | r1_tarski(B_576,C_578)
      | k1_xboole_0 = A_577 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_62423,plain,(
    ! [C_578] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1(C_578,'#skF_4'))
      | r1_tarski('#skF_3',C_578)
      | k1_xboole_0 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_62420])).

tff(c_63210,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_62423])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_63214,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63210,c_32])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_63215,plain,(
    '#skF_1' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63210,c_34])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_186,plain,(
    ! [B_6] : k3_xboole_0(B_6,B_6) = B_6 ),
    inference(resolution,[status(thm)],[c_10,c_166])).

tff(c_62994,plain,(
    ! [A_588,C_589,B_590,D_591] : k3_xboole_0(k2_zfmisc_1(A_588,C_589),k2_zfmisc_1(B_590,D_591)) = k2_zfmisc_1(k3_xboole_0(A_588,B_590),k3_xboole_0(C_589,D_591)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_63062,plain,(
    ! [B_590,D_591] : k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1(B_590,D_591)) = k2_zfmisc_1(k3_xboole_0('#skF_3',B_590),k3_xboole_0('#skF_4',D_591)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_62994])).

tff(c_67450,plain,(
    ! [B_671,D_672] : k2_zfmisc_1(k3_xboole_0('#skF_3',B_671),k3_xboole_0('#skF_4',D_672)) = k2_zfmisc_1(k3_xboole_0('#skF_1',B_671),k3_xboole_0('#skF_2',D_672)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_63062])).

tff(c_67598,plain,(
    ! [B_671] : k2_zfmisc_1(k3_xboole_0('#skF_1',B_671),k3_xboole_0('#skF_2','#skF_4')) = k2_zfmisc_1(k3_xboole_0('#skF_3',B_671),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_67450])).

tff(c_71889,plain,(
    ! [B_706] : k2_zfmisc_1(k3_xboole_0('#skF_1',B_706),k3_xboole_0('#skF_4','#skF_2')) = k2_zfmisc_1(k3_xboole_0('#skF_3',B_706),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_67598])).

tff(c_69010,plain,(
    ! [A_684,C_685,B_686,D_687] : k2_xboole_0(k2_zfmisc_1(A_684,C_685),k2_zfmisc_1(k3_xboole_0(A_684,B_686),k3_xboole_0(C_685,D_687))) = k2_zfmisc_1(A_684,C_685) ),
    inference(superposition,[status(thm),theory(equality)],[c_62994,c_14])).

tff(c_69094,plain,(
    ! [A_684,B_686,C_685,D_687] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_684,B_686),k3_xboole_0(C_685,D_687)),k2_zfmisc_1(A_684,C_685)) ),
    inference(superposition,[status(thm),theory(equality)],[c_69010,c_69])).

tff(c_72045,plain,(
    ! [B_707] : r1_tarski(k2_zfmisc_1(k3_xboole_0('#skF_3',B_707),'#skF_4'),k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_71889,c_69094])).

tff(c_72076,plain,(
    r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_72045])).

tff(c_72100,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_72076])).

tff(c_20,plain,(
    ! [A_15,B_16,C_17] :
      ( ~ r1_tarski(k2_zfmisc_1(A_15,B_16),k2_zfmisc_1(A_15,C_17))
      | r1_tarski(B_16,C_17)
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_63213,plain,(
    ! [A_15,B_16,C_17] :
      ( ~ r1_tarski(k2_zfmisc_1(A_15,B_16),k2_zfmisc_1(A_15,C_17))
      | r1_tarski(B_16,C_17)
      | A_15 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63210,c_20])).

tff(c_72105,plain,
    ( r1_tarski('#skF_2','#skF_4')
    | '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_72100,c_63213])).

tff(c_72116,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_63215,c_72105])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( B_6 = A_5
      | ~ r1_tarski(B_6,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_72121,plain,
    ( '#skF_2' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_72116,c_6])).

tff(c_72130,plain,(
    ~ r1_tarski('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_63214,c_72121])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_72132,plain,(
    k3_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_72116,c_16])).

tff(c_382,plain,(
    ! [B_52,A_53] :
      ( B_52 = A_53
      | ~ r1_tarski(B_52,A_53)
      | ~ r1_tarski(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_64666,plain,(
    ! [B_623,A_624] :
      ( k2_xboole_0(B_623,A_624) = A_624
      | ~ r1_tarski(k2_xboole_0(B_623,A_624),A_624) ) ),
    inference(resolution,[status(thm)],[c_69,c_382])).

tff(c_64720,plain,(
    ! [B_36,A_37] :
      ( k2_xboole_0(B_36,k3_xboole_0(A_37,B_36)) = k3_xboole_0(A_37,B_36)
      | ~ r1_tarski(B_36,k3_xboole_0(A_37,B_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_64666])).

tff(c_65331,plain,(
    ! [A_638,B_639] :
      ( k3_xboole_0(A_638,B_639) = B_639
      | ~ r1_tarski(B_639,k3_xboole_0(A_638,B_639)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_64720])).

tff(c_65376,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(B_4,k3_xboole_0(B_4,A_3)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_65331])).

tff(c_72163,plain,
    ( k3_xboole_0('#skF_4','#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_72132,c_65376])).

tff(c_72254,plain,(
    k3_xboole_0('#skF_4','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_72163])).

tff(c_64571,plain,(
    ! [C_620,B_621,A_622] : r1_tarski(k2_zfmisc_1(C_620,B_621),k2_zfmisc_1(C_620,k2_xboole_0(A_622,B_621))) ),
    inference(superposition,[status(thm),theory(equality)],[c_61757,c_69])).

tff(c_65609,plain,(
    ! [C_647,A_648,B_649] : r1_tarski(k2_zfmisc_1(C_647,k3_xboole_0(A_648,B_649)),k2_zfmisc_1(C_647,B_649)) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_64571])).

tff(c_65668,plain,(
    ! [A_648] : r1_tarski(k2_zfmisc_1('#skF_3',k3_xboole_0(A_648,'#skF_4')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_65609])).

tff(c_72165,plain,(
    r1_tarski(k2_zfmisc_1('#skF_3','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_72132,c_65668])).

tff(c_22,plain,(
    ! [B_16,A_15,C_17] :
      ( ~ r1_tarski(k2_zfmisc_1(B_16,A_15),k2_zfmisc_1(C_17,A_15))
      | r1_tarski(B_16,C_17)
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_63211,plain,(
    ! [B_16,A_15,C_17] :
      ( ~ r1_tarski(k2_zfmisc_1(B_16,A_15),k2_zfmisc_1(C_17,A_15))
      | r1_tarski(B_16,C_17)
      | A_15 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63210,c_22])).

tff(c_73036,plain,
    ( r1_tarski('#skF_3','#skF_1')
    | '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_72165,c_63211])).

tff(c_73050,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_63214,c_73036])).

tff(c_73068,plain,(
    k3_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_73050,c_16])).

tff(c_73927,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_73068])).

tff(c_63065,plain,(
    ! [A_588,C_589] : k3_xboole_0(k2_zfmisc_1(A_588,C_589),k2_zfmisc_1('#skF_1','#skF_2')) = k2_zfmisc_1(k3_xboole_0(A_588,'#skF_3'),k3_xboole_0(C_589,'#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_62994])).

tff(c_66758,plain,(
    ! [A_666,C_667] : k2_zfmisc_1(k3_xboole_0(A_666,'#skF_3'),k3_xboole_0(C_667,'#skF_4')) = k2_zfmisc_1(k3_xboole_0(A_666,'#skF_1'),k3_xboole_0(C_667,'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_63065])).

tff(c_66894,plain,(
    ! [C_667] : k2_zfmisc_1(k3_xboole_0('#skF_3','#skF_1'),k3_xboole_0(C_667,'#skF_2')) = k2_zfmisc_1('#skF_3',k3_xboole_0(C_667,'#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_66758])).

tff(c_66931,plain,(
    ! [C_667] : k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0(C_667,'#skF_2')) = k2_zfmisc_1('#skF_3',k3_xboole_0(C_667,'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_66894])).

tff(c_75523,plain,(
    ! [C_727] : k2_zfmisc_1('#skF_3',k3_xboole_0(C_727,'#skF_2')) = k2_zfmisc_1('#skF_3',k3_xboole_0(C_727,'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73927,c_66931])).

tff(c_75659,plain,(
    k2_zfmisc_1('#skF_3',k3_xboole_0('#skF_4','#skF_4')) = k2_zfmisc_1('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_72254,c_75523])).

tff(c_75723,plain,(
    k2_zfmisc_1('#skF_3','#skF_2') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_186,c_75659])).

tff(c_2463,plain,(
    ! [A_102] : k2_xboole_0(k2_zfmisc_1(A_102,'#skF_4'),k2_zfmisc_1('#skF_1','#skF_2')) = k2_zfmisc_1(k2_xboole_0(A_102,'#skF_3'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_874])).

tff(c_2476,plain,(
    k2_zfmisc_1(k2_xboole_0('#skF_1','#skF_3'),'#skF_4') = k2_zfmisc_1('#skF_1',k2_xboole_0('#skF_4','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2463,c_26])).

tff(c_1261,plain,(
    ! [A_78,B_79] : k3_xboole_0(k3_xboole_0(A_78,B_79),B_79) = k3_xboole_0(A_78,B_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_328])).

tff(c_2316,plain,(
    ! [A_100,B_101] : k3_xboole_0(k3_xboole_0(A_100,B_101),A_100) = k3_xboole_0(B_101,A_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1261])).

tff(c_2413,plain,(
    ! [A_1,B_2] : k3_xboole_0(k2_xboole_0(A_1,B_2),B_2) = k3_xboole_0(B_2,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_2316])).

tff(c_2458,plain,(
    ! [A_1,B_2] : k3_xboole_0(k2_xboole_0(A_1,B_2),B_2) = B_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_2413])).

tff(c_2851,plain,(
    ! [A_107,C_108,B_109,D_110] : k3_xboole_0(k2_zfmisc_1(A_107,C_108),k2_zfmisc_1(B_109,D_110)) = k2_zfmisc_1(k3_xboole_0(A_107,B_109),k3_xboole_0(C_108,D_110)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2897,plain,(
    ! [B_109,D_110,A_107,C_108] : k3_xboole_0(k2_zfmisc_1(B_109,D_110),k2_zfmisc_1(A_107,C_108)) = k2_zfmisc_1(k3_xboole_0(A_107,B_109),k3_xboole_0(C_108,D_110)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2851,c_4])).

tff(c_663,plain,(
    ! [A_1,B_2] : k2_xboole_0(k2_xboole_0(A_1,B_2),B_2) = k2_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_605])).

tff(c_57124,plain,(
    ! [A_537] : k3_xboole_0(k2_zfmisc_1(A_537,'#skF_4'),k2_zfmisc_1(k2_xboole_0(A_537,'#skF_3'),'#skF_4')) = k2_zfmisc_1(A_537,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2463,c_185])).

tff(c_57251,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_1',k2_xboole_0('#skF_4','#skF_2')),k2_zfmisc_1(k2_xboole_0(k2_xboole_0('#skF_1','#skF_3'),'#skF_3'),'#skF_4')) = k2_zfmisc_1(k2_xboole_0('#skF_1','#skF_3'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2476,c_57124])).

tff(c_57336,plain,(
    k2_zfmisc_1('#skF_1',k2_xboole_0('#skF_4','#skF_2')) = k2_zfmisc_1('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2476,c_185,c_2458,c_2897,c_663,c_57251])).

tff(c_1491,plain,(
    ! [C_82,A_83,B_84] : k2_xboole_0(k2_zfmisc_1(C_82,A_83),k2_zfmisc_1(C_82,B_84)) = k2_zfmisc_1(C_82,k2_xboole_0(A_83,B_84)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3041,plain,(
    ! [C_112,A_113,B_114] : r1_tarski(k2_zfmisc_1(C_112,A_113),k2_zfmisc_1(C_112,k2_xboole_0(A_113,B_114))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1491,c_18])).

tff(c_3106,plain,(
    ! [C_112,B_2,A_1] : r1_tarski(k2_zfmisc_1(C_112,B_2),k2_zfmisc_1(C_112,k2_xboole_0(A_1,B_2))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3041])).

tff(c_57395,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_57336,c_3106])).

tff(c_532,plain,(
    ! [A_58,B_59,C_60] :
      ( ~ r1_tarski(k2_zfmisc_1(A_58,B_59),k2_zfmisc_1(A_58,C_60))
      | r1_tarski(B_59,C_60)
      | k1_xboole_0 = A_58 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_538,plain,(
    ! [B_59] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_3',B_59),k2_zfmisc_1('#skF_1','#skF_2'))
      | r1_tarski(B_59,'#skF_4')
      | k1_xboole_0 = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_532])).

tff(c_1123,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_538])).

tff(c_2193,plain,(
    ! [B_95,A_96,C_97] :
      ( ~ r1_tarski(k2_zfmisc_1(B_95,A_96),k2_zfmisc_1(C_97,A_96))
      | r1_tarski(B_95,C_97)
      | A_96 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1123,c_22])).

tff(c_2196,plain,(
    ! [C_97] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1(C_97,'#skF_4'))
      | r1_tarski('#skF_3',C_97)
      | '#skF_3' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_2193])).

tff(c_6750,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2196])).

tff(c_6772,plain,(
    '#skF_1' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6750,c_39])).

tff(c_6771,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k2_zfmisc_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6750,c_36])).

tff(c_2943,plain,(
    ! [B_111] : k2_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1(B_111,'#skF_4')) = k2_zfmisc_1(k2_xboole_0('#skF_3',B_111),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_874])).

tff(c_2992,plain,(
    ! [B_111] : k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1(k2_xboole_0('#skF_3',B_111),'#skF_4')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2943,c_185])).

tff(c_15133,plain,(
    ! [B_250] : k2_zfmisc_1(k3_xboole_0('#skF_1',k2_xboole_0('#skF_4',B_250)),k3_xboole_0('#skF_4','#skF_2')) = k2_zfmisc_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6771,c_4,c_28,c_6750,c_2992])).

tff(c_6235,plain,(
    ! [A_179,C_180,B_181,D_182] : k2_xboole_0(k2_zfmisc_1(A_179,C_180),k2_zfmisc_1(k3_xboole_0(A_179,B_181),k3_xboole_0(C_180,D_182))) = k2_zfmisc_1(A_179,C_180) ),
    inference(superposition,[status(thm),theory(equality)],[c_2851,c_14])).

tff(c_6307,plain,(
    ! [A_179,B_181,C_180,D_182] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_179,B_181),k3_xboole_0(C_180,D_182)),k2_zfmisc_1(A_179,C_180)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6235,c_69])).

tff(c_15159,plain,(
    r1_tarski(k2_zfmisc_1('#skF_4','#skF_4'),k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_15133,c_6307])).

tff(c_1124,plain,(
    ! [A_15,B_16,C_17] :
      ( ~ r1_tarski(k2_zfmisc_1(A_15,B_16),k2_zfmisc_1(A_15,C_17))
      | r1_tarski(B_16,C_17)
      | A_15 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1123,c_20])).

tff(c_17375,plain,(
    ! [A_254,B_255,C_256] :
      ( ~ r1_tarski(k2_zfmisc_1(A_254,B_255),k2_zfmisc_1(A_254,C_256))
      | r1_tarski(B_255,C_256)
      | A_254 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6750,c_1124])).

tff(c_17477,plain,(
    ! [C_256] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_4'),k2_zfmisc_1('#skF_1',C_256))
      | r1_tarski('#skF_2',C_256)
      | '#skF_1' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6771,c_17375])).

tff(c_17519,plain,(
    ! [C_257] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_4'),k2_zfmisc_1('#skF_1',C_257))
      | r1_tarski('#skF_2',C_257) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6772,c_17477])).

tff(c_17550,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_15159,c_17519])).

tff(c_17569,plain,(
    k3_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_17550,c_16])).

tff(c_4422,plain,(
    ! [C_140,B_141,A_142] : r1_tarski(k2_zfmisc_1(C_140,B_141),k2_zfmisc_1(C_140,k2_xboole_0(A_142,B_141))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3041])).

tff(c_4484,plain,(
    ! [C_140,A_37,B_36] : r1_tarski(k2_zfmisc_1(C_140,k3_xboole_0(A_37,B_36)),k2_zfmisc_1(C_140,B_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_4422])).

tff(c_17836,plain,(
    ! [C_140] : r1_tarski(k2_zfmisc_1(C_140,'#skF_2'),k2_zfmisc_1(C_140,'#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_17569,c_4484])).

tff(c_1125,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1123,c_32])).

tff(c_6769,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6750,c_1125])).

tff(c_2192,plain,(
    ! [B_16,A_15,C_17] :
      ( ~ r1_tarski(k2_zfmisc_1(B_16,A_15),k2_zfmisc_1(C_17,A_15))
      | r1_tarski(B_16,C_17)
      | A_15 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1123,c_22])).

tff(c_18298,plain,(
    ! [B_258,A_259,C_260] :
      ( ~ r1_tarski(k2_zfmisc_1(B_258,A_259),k2_zfmisc_1(C_260,A_259))
      | r1_tarski(B_258,C_260)
      | A_259 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6750,c_2192])).

tff(c_18373,plain,(
    ! [B_258] :
      ( ~ r1_tarski(k2_zfmisc_1(B_258,'#skF_2'),k2_zfmisc_1('#skF_4','#skF_4'))
      | r1_tarski(B_258,'#skF_1')
      | '#skF_2' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6771,c_18298])).

tff(c_23724,plain,(
    ! [B_335] :
      ( ~ r1_tarski(k2_zfmisc_1(B_335,'#skF_2'),k2_zfmisc_1('#skF_4','#skF_4'))
      | r1_tarski(B_335,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_6769,c_18373])).

tff(c_23777,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_17836,c_23724])).

tff(c_23793,plain,
    ( '#skF_1' = '#skF_4'
    | ~ r1_tarski('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_23777,c_6])).

tff(c_23802,plain,(
    ~ r1_tarski('#skF_1','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_6772,c_23793])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_17568,plain,(
    k2_xboole_0('#skF_2','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_17550,c_12])).

tff(c_17718,plain,(
    k2_xboole_0('#skF_4','#skF_2') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_17568])).

tff(c_3568,plain,(
    ! [B_122] : k2_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3',B_122)) = k2_zfmisc_1('#skF_3',k2_xboole_0('#skF_4',B_122)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1491])).

tff(c_3627,plain,(
    ! [B_122] : k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3',k2_xboole_0('#skF_4',B_122))) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3568,c_185])).

tff(c_14529,plain,(
    ! [B_249] : k2_zfmisc_1(k3_xboole_0('#skF_4','#skF_1'),k3_xboole_0('#skF_2',k2_xboole_0('#skF_4',B_249))) = k2_zfmisc_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6771,c_4,c_28,c_6750,c_3627])).

tff(c_2906,plain,(
    ! [A_107,C_108,B_109,D_110] : k2_xboole_0(k2_zfmisc_1(A_107,C_108),k2_zfmisc_1(k3_xboole_0(A_107,B_109),k3_xboole_0(C_108,D_110))) = k2_zfmisc_1(A_107,C_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_2851,c_14])).

tff(c_14570,plain,(
    k2_xboole_0(k2_zfmisc_1('#skF_4','#skF_2'),k2_zfmisc_1('#skF_4','#skF_4')) = k2_zfmisc_1('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_14529,c_2906])).

tff(c_259,plain,(
    ! [A_46,B_47] :
      ( k2_xboole_0(A_46,B_47) = B_47
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_546,plain,(
    ! [A_61,B_62] : k2_xboole_0(A_61,k2_xboole_0(A_61,B_62)) = k2_xboole_0(A_61,B_62) ),
    inference(resolution,[status(thm)],[c_18,c_259])).

tff(c_775,plain,(
    ! [A_67,B_68] : k2_xboole_0(A_67,k2_xboole_0(B_68,A_67)) = k2_xboole_0(A_67,B_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_546])).

tff(c_800,plain,(
    ! [B_68,A_67] : k3_xboole_0(k2_xboole_0(B_68,A_67),k2_xboole_0(A_67,B_68)) = k2_xboole_0(B_68,A_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_775,c_248])).

tff(c_14864,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_4','#skF_2'),k2_xboole_0(k2_zfmisc_1('#skF_4','#skF_4'),k2_zfmisc_1('#skF_4','#skF_2'))) = k2_xboole_0(k2_zfmisc_1('#skF_4','#skF_2'),k2_zfmisc_1('#skF_4','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14570,c_800])).

tff(c_14990,plain,(
    k2_zfmisc_1('#skF_4',k2_xboole_0('#skF_4','#skF_2')) = k2_zfmisc_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_248,c_2,c_14864])).

tff(c_17945,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') = k2_zfmisc_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17718,c_14990])).

tff(c_18370,plain,(
    ! [C_260] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_4'),k2_zfmisc_1(C_260,'#skF_2'))
      | r1_tarski('#skF_1',C_260)
      | '#skF_2' = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6771,c_18298])).

tff(c_51448,plain,(
    ! [C_497] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_4'),k2_zfmisc_1(C_497,'#skF_2'))
      | r1_tarski('#skF_1',C_497) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6769,c_18370])).

tff(c_51468,plain,
    ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_4'),k2_zfmisc_1('#skF_4','#skF_4'))
    | r1_tarski('#skF_1','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_17945,c_51448])).

tff(c_51494,plain,(
    r1_tarski('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_51468])).

tff(c_51496,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23802,c_51494])).

tff(c_51497,plain,(
    ! [C_97] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1(C_97,'#skF_4'))
      | r1_tarski('#skF_3',C_97) ) ),
    inference(splitRight,[status(thm)],[c_2196])).

tff(c_57476,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_57395,c_51497])).

tff(c_57484,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_57476,c_6])).

tff(c_57493,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_57484])).

tff(c_57495,plain,(
    k3_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_57476,c_16])).

tff(c_58558,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_57495])).

tff(c_57467,plain,
    ( r1_tarski('#skF_2','#skF_4')
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_57395,c_1124])).

tff(c_57479,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_57467])).

tff(c_57505,plain,(
    k2_xboole_0('#skF_2','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_57479,c_12])).

tff(c_2416,plain,(
    ! [A_13,B_14] : k3_xboole_0(k2_xboole_0(A_13,B_14),A_13) = k3_xboole_0(A_13,A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_2316])).

tff(c_2459,plain,(
    ! [A_13,B_14] : k3_xboole_0(k2_xboole_0(A_13,B_14),A_13) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_2416])).

tff(c_58226,plain,(
    k3_xboole_0('#skF_4','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_57505,c_2459])).

tff(c_2922,plain,(
    ! [B_109,D_110] : k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1(B_109,D_110)) = k2_zfmisc_1(k3_xboole_0('#skF_3',B_109),k3_xboole_0('#skF_4',D_110)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_2851])).

tff(c_52161,plain,(
    ! [B_502,D_503] : k2_zfmisc_1(k3_xboole_0('#skF_3',B_502),k3_xboole_0('#skF_4',D_503)) = k2_zfmisc_1(k3_xboole_0('#skF_1',B_502),k3_xboole_0('#skF_2',D_503)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2922])).

tff(c_52313,plain,(
    ! [B_502] : k2_zfmisc_1(k3_xboole_0('#skF_1',B_502),k3_xboole_0('#skF_2','#skF_4')) = k2_zfmisc_1(k3_xboole_0('#skF_3',B_502),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_52161])).

tff(c_52342,plain,(
    ! [B_502] : k2_zfmisc_1(k3_xboole_0('#skF_1',B_502),k3_xboole_0('#skF_4','#skF_2')) = k2_zfmisc_1(k3_xboole_0('#skF_3',B_502),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_52313])).

tff(c_59239,plain,(
    ! [B_542] : k2_zfmisc_1(k3_xboole_0('#skF_3',B_542),'#skF_4') = k2_zfmisc_1(k3_xboole_0('#skF_1',B_542),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58226,c_52342])).

tff(c_59391,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_59239])).

tff(c_59426,plain,(
    k2_zfmisc_1('#skF_3','#skF_2') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58558,c_36,c_59391])).

tff(c_60615,plain,(
    ! [B_16] :
      ( ~ r1_tarski(k2_zfmisc_1(B_16,'#skF_2'),k2_zfmisc_1('#skF_1','#skF_2'))
      | r1_tarski(B_16,'#skF_3')
      | '#skF_2' = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59426,c_2192])).

tff(c_61362,plain,(
    ! [B_557] :
      ( ~ r1_tarski(k2_zfmisc_1(B_557,'#skF_2'),k2_zfmisc_1('#skF_1','#skF_2'))
      | r1_tarski(B_557,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1125,c_60615])).

tff(c_61385,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_61362])).

tff(c_61393,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57493,c_61385])).

tff(c_61395,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_538])).

tff(c_535,plain,(
    ! [C_60] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3',C_60))
      | r1_tarski('#skF_4',C_60)
      | k1_xboole_0 = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_532])).

tff(c_62553,plain,(
    ! [C_60] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3',C_60))
      | r1_tarski('#skF_4',C_60) ) ),
    inference(negUnitSimplification,[status(thm)],[c_61395,c_535])).

tff(c_75953,plain,
    ( ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2'))
    | r1_tarski('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_75723,c_62553])).

tff(c_75998,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_75953])).

tff(c_76000,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72130,c_75998])).

tff(c_76001,plain,(
    ! [C_578] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1(C_578,'#skF_4'))
      | r1_tarski('#skF_3',C_578) ) ),
    inference(splitRight,[status(thm)],[c_62423])).

tff(c_82439,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_82370,c_76001])).

tff(c_82458,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_82439,c_6])).

tff(c_82467,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_82458])).

tff(c_82430,plain,
    ( r1_tarski('#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_82370,c_20])).

tff(c_82442,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_82430])).

tff(c_82454,plain,
    ( '#skF_2' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_82442,c_6])).

tff(c_83777,plain,(
    ~ r1_tarski('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_82454])).

tff(c_82468,plain,(
    k2_xboole_0('#skF_3','#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_82439,c_12])).

tff(c_83132,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_82468,c_62159])).

tff(c_82455,plain,(
    k2_xboole_0('#skF_2','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_82442,c_12])).

tff(c_82706,plain,(
    k3_xboole_0('#skF_4','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_82455,c_62159])).

tff(c_187,plain,(
    ! [B_42] : k3_xboole_0(B_42,B_42) = B_42 ),
    inference(resolution,[status(thm)],[c_10,c_166])).

tff(c_199,plain,(
    ! [B_42] : k2_xboole_0(B_42,B_42) = B_42 ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_14])).

tff(c_82281,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_3'),'#skF_4')) = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_82130])).

tff(c_82326,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_4','#skF_2')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4,c_28,c_199,c_82281])).

tff(c_85026,plain,(
    k2_zfmisc_1('#skF_3','#skF_2') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83132,c_82706,c_82326])).

tff(c_85111,plain,
    ( ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k2_zfmisc_1('#skF_1','#skF_2'))
    | r1_tarski('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_85026,c_62553])).

tff(c_85161,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_85111])).

tff(c_85163,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83777,c_85161])).

tff(c_85164,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_82454])).

tff(c_76002,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_62423])).

tff(c_62426,plain,(
    ! [B_576] :
      ( ~ r1_tarski(k2_zfmisc_1(B_576,'#skF_4'),k2_zfmisc_1('#skF_1','#skF_2'))
      | r1_tarski(B_576,'#skF_3')
      | k1_xboole_0 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_62420])).

tff(c_78784,plain,(
    ! [B_576] :
      ( ~ r1_tarski(k2_zfmisc_1(B_576,'#skF_4'),k2_zfmisc_1('#skF_1','#skF_2'))
      | r1_tarski(B_576,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_76002,c_62426])).

tff(c_107417,plain,(
    ! [B_1022] :
      ( ~ r1_tarski(k2_zfmisc_1(B_1022,'#skF_4'),k2_zfmisc_1('#skF_1','#skF_4'))
      | r1_tarski(B_1022,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85164,c_78784])).

tff(c_107481,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_107417])).

tff(c_107503,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82467,c_107481])).

tff(c_107504,plain,(
    '#skF_2' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_107505,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_107550,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k2_zfmisc_1('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107505,c_36])).

tff(c_108873,plain,(
    ! [A_1078,B_1079,C_1080] :
      ( ~ r1_tarski(k2_zfmisc_1(A_1078,B_1079),k2_zfmisc_1(A_1078,C_1080))
      | r1_tarski(B_1079,C_1080)
      | k1_xboole_0 = A_1078 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_108879,plain,(
    ! [B_1079] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1',B_1079),k2_zfmisc_1('#skF_1','#skF_4'))
      | r1_tarski(B_1079,'#skF_2')
      | k1_xboole_0 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107550,c_108873])).

tff(c_109925,plain,(
    ! [B_1101] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1',B_1101),k2_zfmisc_1('#skF_1','#skF_4'))
      | r1_tarski(B_1101,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_108879])).

tff(c_109935,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_109925])).

tff(c_109937,plain,
    ( '#skF_2' = '#skF_4'
    | ~ r1_tarski('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_109935,c_6])).

tff(c_109946,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_107504,c_109937])).

tff(c_108876,plain,(
    ! [C_1080] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_4'),k2_zfmisc_1('#skF_1',C_1080))
      | r1_tarski('#skF_2',C_1080)
      | k1_xboole_0 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107550,c_108873])).

tff(c_110304,plain,(
    ! [C_1106] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_4'),k2_zfmisc_1('#skF_1',C_1106))
      | r1_tarski('#skF_2',C_1106) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_108876])).

tff(c_110311,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_110304])).

tff(c_110317,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109946,c_110311])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n001.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 18:11:00 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 25.33/16.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.33/16.07  
% 25.33/16.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.33/16.07  %$ r1_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 25.33/16.07  
% 25.33/16.07  %Foreground sorts:
% 25.33/16.07  
% 25.33/16.07  
% 25.33/16.07  %Background operators:
% 25.33/16.07  
% 25.33/16.07  
% 25.33/16.07  %Foreground operators:
% 25.33/16.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 25.33/16.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 25.33/16.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 25.33/16.07  tff('#skF_2', type, '#skF_2': $i).
% 25.33/16.07  tff('#skF_3', type, '#skF_3': $i).
% 25.33/16.07  tff('#skF_1', type, '#skF_1': $i).
% 25.33/16.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 25.33/16.07  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 25.33/16.07  tff('#skF_4', type, '#skF_4': $i).
% 25.33/16.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 25.33/16.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 25.33/16.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 25.33/16.07  
% 25.56/16.10  tff(f_75, negated_conjecture, ~(![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 25.56/16.10  tff(f_62, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 25.56/16.10  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 25.56/16.10  tff(f_47, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 25.56/16.10  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 25.56/16.10  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 25.56/16.10  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 25.56/16.10  tff(f_64, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 25.56/16.10  tff(f_58, axiom, (![A, B, C]: ~((~(A = k1_xboole_0) & (r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(C, A)) | r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(A, C)))) & ~r1_tarski(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 25.56/16.10  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 25.56/16.10  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 25.56/16.10  tff(c_30, plain, ('#skF_2'!='#skF_4' | '#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_75])).
% 25.56/16.10  tff(c_39, plain, ('#skF_3'!='#skF_1'), inference(splitLeft, [status(thm)], [c_30])).
% 25.56/16.10  tff(c_26, plain, (![C_20, A_18, B_19]: (k2_xboole_0(k2_zfmisc_1(C_20, A_18), k2_zfmisc_1(C_20, B_19))=k2_zfmisc_1(C_20, k2_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 25.56/16.10  tff(c_36, plain, (k2_zfmisc_1('#skF_3', '#skF_4')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 25.56/16.10  tff(c_874, plain, (![A_69, C_70, B_71]: (k2_xboole_0(k2_zfmisc_1(A_69, C_70), k2_zfmisc_1(B_71, C_70))=k2_zfmisc_1(k2_xboole_0(A_69, B_71), C_70))), inference(cnfTransformation, [status(thm)], [f_62])).
% 25.56/16.10  tff(c_76676, plain, (![A_744]: (k2_xboole_0(k2_zfmisc_1(A_744, '#skF_4'), k2_zfmisc_1('#skF_1', '#skF_2'))=k2_zfmisc_1(k2_xboole_0(A_744, '#skF_3'), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_874])).
% 25.56/16.10  tff(c_76761, plain, (k2_zfmisc_1(k2_xboole_0('#skF_1', '#skF_3'), '#skF_4')=k2_zfmisc_1('#skF_1', k2_xboole_0('#skF_4', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_26, c_76676])).
% 25.56/16.10  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 25.56/16.10  tff(c_18, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 25.56/16.10  tff(c_166, plain, (![A_40, B_41]: (k3_xboole_0(A_40, B_41)=A_40 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_45])).
% 25.56/16.10  tff(c_224, plain, (![A_44, B_45]: (k3_xboole_0(A_44, k2_xboole_0(A_44, B_45))=A_44)), inference(resolution, [status(thm)], [c_18, c_166])).
% 25.56/16.10  tff(c_248, plain, (![B_2, A_1]: (k3_xboole_0(B_2, k2_xboole_0(A_1, B_2))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_224])).
% 25.56/16.10  tff(c_185, plain, (![A_13, B_14]: (k3_xboole_0(A_13, k2_xboole_0(A_13, B_14))=A_13)), inference(resolution, [status(thm)], [c_18, c_166])).
% 25.56/16.10  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 25.56/16.10  tff(c_111, plain, (![B_36, A_37]: (k3_xboole_0(B_36, A_37)=k3_xboole_0(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_29])).
% 25.56/16.10  tff(c_14, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k3_xboole_0(A_9, B_10))=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 25.56/16.10  tff(c_135, plain, (![B_36, A_37]: (k2_xboole_0(B_36, k3_xboole_0(A_37, B_36))=B_36)), inference(superposition, [status(thm), theory('equality')], [c_111, c_14])).
% 25.56/16.10  tff(c_328, plain, (![B_50, A_51]: (k3_xboole_0(B_50, k2_xboole_0(A_51, B_50))=B_50)), inference(superposition, [status(thm), theory('equality')], [c_2, c_224])).
% 25.56/16.10  tff(c_61665, plain, (![A_562, B_563]: (k3_xboole_0(k3_xboole_0(A_562, B_563), B_563)=k3_xboole_0(A_562, B_563))), inference(superposition, [status(thm), theory('equality')], [c_135, c_328])).
% 25.56/16.10  tff(c_62086, plain, (![B_570, A_571]: (k3_xboole_0(B_570, k3_xboole_0(A_571, B_570))=k3_xboole_0(A_571, B_570))), inference(superposition, [status(thm), theory('equality')], [c_4, c_61665])).
% 25.56/16.10  tff(c_62134, plain, (![A_13, B_14]: (k3_xboole_0(k2_xboole_0(A_13, B_14), A_13)=k3_xboole_0(A_13, k2_xboole_0(A_13, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_185, c_62086])).
% 25.56/16.10  tff(c_62159, plain, (![A_13, B_14]: (k3_xboole_0(k2_xboole_0(A_13, B_14), A_13)=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_185, c_62134])).
% 25.56/16.10  tff(c_28, plain, (![A_21, C_23, B_22, D_24]: (k3_xboole_0(k2_zfmisc_1(A_21, C_23), k2_zfmisc_1(B_22, D_24))=k2_zfmisc_1(k3_xboole_0(A_21, B_22), k3_xboole_0(C_23, D_24)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 25.56/16.10  tff(c_281, plain, (![B_48, A_49]: (k2_xboole_0(B_48, k3_xboole_0(A_49, B_48))=B_48)), inference(superposition, [status(thm), theory('equality')], [c_111, c_14])).
% 25.56/16.10  tff(c_605, plain, (![A_63, B_64]: (k2_xboole_0(k2_xboole_0(A_63, B_64), A_63)=k2_xboole_0(A_63, B_64))), inference(superposition, [status(thm), theory('equality')], [c_185, c_281])).
% 25.56/16.10  tff(c_656, plain, (![B_2, A_1]: (k2_xboole_0(k2_xboole_0(B_2, A_1), A_1)=k2_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_605])).
% 25.56/16.10  tff(c_82130, plain, (![A_822]: (k3_xboole_0(k2_zfmisc_1(A_822, '#skF_4'), k2_zfmisc_1(k2_xboole_0(A_822, '#skF_3'), '#skF_4'))=k2_zfmisc_1(A_822, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_76676, c_185])).
% 25.56/16.10  tff(c_82223, plain, (k3_xboole_0(k2_zfmisc_1('#skF_1', k2_xboole_0('#skF_4', '#skF_2')), k2_zfmisc_1(k2_xboole_0(k2_xboole_0('#skF_1', '#skF_3'), '#skF_3'), '#skF_4'))=k2_zfmisc_1(k2_xboole_0('#skF_1', '#skF_3'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_76761, c_82130])).
% 25.56/16.10  tff(c_82316, plain, (k2_zfmisc_1('#skF_1', k2_xboole_0('#skF_4', '#skF_2'))=k2_zfmisc_1('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76761, c_248, c_62159, c_28, c_656, c_82223])).
% 25.56/16.10  tff(c_61757, plain, (![C_564, A_565, B_566]: (k2_xboole_0(k2_zfmisc_1(C_564, A_565), k2_zfmisc_1(C_564, B_566))=k2_zfmisc_1(C_564, k2_xboole_0(A_565, B_566)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 25.56/16.10  tff(c_54, plain, (![B_30, A_31]: (k2_xboole_0(B_30, A_31)=k2_xboole_0(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_27])).
% 25.56/16.10  tff(c_69, plain, (![A_31, B_30]: (r1_tarski(A_31, k2_xboole_0(B_30, A_31)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_18])).
% 25.56/16.10  tff(c_61801, plain, (![C_564, B_566, A_565]: (r1_tarski(k2_zfmisc_1(C_564, B_566), k2_zfmisc_1(C_564, k2_xboole_0(A_565, B_566))))), inference(superposition, [status(thm), theory('equality')], [c_61757, c_69])).
% 25.56/16.10  tff(c_82370, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_82316, c_61801])).
% 25.56/16.10  tff(c_62420, plain, (![B_576, A_577, C_578]: (~r1_tarski(k2_zfmisc_1(B_576, A_577), k2_zfmisc_1(C_578, A_577)) | r1_tarski(B_576, C_578) | k1_xboole_0=A_577)), inference(cnfTransformation, [status(thm)], [f_58])).
% 25.56/16.10  tff(c_62423, plain, (![C_578]: (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1(C_578, '#skF_4')) | r1_tarski('#skF_3', C_578) | k1_xboole_0='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_36, c_62420])).
% 25.56/16.10  tff(c_63210, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_62423])).
% 25.56/16.10  tff(c_32, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_75])).
% 25.56/16.10  tff(c_63214, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_63210, c_32])).
% 25.56/16.10  tff(c_34, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_75])).
% 25.56/16.10  tff(c_63215, plain, ('#skF_1'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_63210, c_34])).
% 25.56/16.10  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 25.56/16.10  tff(c_186, plain, (![B_6]: (k3_xboole_0(B_6, B_6)=B_6)), inference(resolution, [status(thm)], [c_10, c_166])).
% 25.56/16.10  tff(c_62994, plain, (![A_588, C_589, B_590, D_591]: (k3_xboole_0(k2_zfmisc_1(A_588, C_589), k2_zfmisc_1(B_590, D_591))=k2_zfmisc_1(k3_xboole_0(A_588, B_590), k3_xboole_0(C_589, D_591)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 25.56/16.10  tff(c_63062, plain, (![B_590, D_591]: (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1(B_590, D_591))=k2_zfmisc_1(k3_xboole_0('#skF_3', B_590), k3_xboole_0('#skF_4', D_591)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_62994])).
% 25.56/16.10  tff(c_67450, plain, (![B_671, D_672]: (k2_zfmisc_1(k3_xboole_0('#skF_3', B_671), k3_xboole_0('#skF_4', D_672))=k2_zfmisc_1(k3_xboole_0('#skF_1', B_671), k3_xboole_0('#skF_2', D_672)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_63062])).
% 25.56/16.10  tff(c_67598, plain, (![B_671]: (k2_zfmisc_1(k3_xboole_0('#skF_1', B_671), k3_xboole_0('#skF_2', '#skF_4'))=k2_zfmisc_1(k3_xboole_0('#skF_3', B_671), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_186, c_67450])).
% 25.56/16.10  tff(c_71889, plain, (![B_706]: (k2_zfmisc_1(k3_xboole_0('#skF_1', B_706), k3_xboole_0('#skF_4', '#skF_2'))=k2_zfmisc_1(k3_xboole_0('#skF_3', B_706), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_67598])).
% 25.56/16.10  tff(c_69010, plain, (![A_684, C_685, B_686, D_687]: (k2_xboole_0(k2_zfmisc_1(A_684, C_685), k2_zfmisc_1(k3_xboole_0(A_684, B_686), k3_xboole_0(C_685, D_687)))=k2_zfmisc_1(A_684, C_685))), inference(superposition, [status(thm), theory('equality')], [c_62994, c_14])).
% 25.56/16.10  tff(c_69094, plain, (![A_684, B_686, C_685, D_687]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_684, B_686), k3_xboole_0(C_685, D_687)), k2_zfmisc_1(A_684, C_685)))), inference(superposition, [status(thm), theory('equality')], [c_69010, c_69])).
% 25.56/16.10  tff(c_72045, plain, (![B_707]: (r1_tarski(k2_zfmisc_1(k3_xboole_0('#skF_3', B_707), '#skF_4'), k2_zfmisc_1('#skF_1', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_71889, c_69094])).
% 25.56/16.10  tff(c_72076, plain, (r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_1', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_248, c_72045])).
% 25.56/16.11  tff(c_72100, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_72076])).
% 25.56/16.11  tff(c_20, plain, (![A_15, B_16, C_17]: (~r1_tarski(k2_zfmisc_1(A_15, B_16), k2_zfmisc_1(A_15, C_17)) | r1_tarski(B_16, C_17) | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_58])).
% 25.56/16.11  tff(c_63213, plain, (![A_15, B_16, C_17]: (~r1_tarski(k2_zfmisc_1(A_15, B_16), k2_zfmisc_1(A_15, C_17)) | r1_tarski(B_16, C_17) | A_15='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_63210, c_20])).
% 25.56/16.11  tff(c_72105, plain, (r1_tarski('#skF_2', '#skF_4') | '#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_72100, c_63213])).
% 25.56/16.11  tff(c_72116, plain, (r1_tarski('#skF_2', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_63215, c_72105])).
% 25.56/16.11  tff(c_6, plain, (![B_6, A_5]: (B_6=A_5 | ~r1_tarski(B_6, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 25.56/16.11  tff(c_72121, plain, ('#skF_2'='#skF_4' | ~r1_tarski('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_72116, c_6])).
% 25.56/16.11  tff(c_72130, plain, (~r1_tarski('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_63214, c_72121])).
% 25.56/16.11  tff(c_16, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 25.56/16.11  tff(c_72132, plain, (k3_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(resolution, [status(thm)], [c_72116, c_16])).
% 25.56/16.11  tff(c_382, plain, (![B_52, A_53]: (B_52=A_53 | ~r1_tarski(B_52, A_53) | ~r1_tarski(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_35])).
% 25.56/16.11  tff(c_64666, plain, (![B_623, A_624]: (k2_xboole_0(B_623, A_624)=A_624 | ~r1_tarski(k2_xboole_0(B_623, A_624), A_624))), inference(resolution, [status(thm)], [c_69, c_382])).
% 25.56/16.11  tff(c_64720, plain, (![B_36, A_37]: (k2_xboole_0(B_36, k3_xboole_0(A_37, B_36))=k3_xboole_0(A_37, B_36) | ~r1_tarski(B_36, k3_xboole_0(A_37, B_36)))), inference(superposition, [status(thm), theory('equality')], [c_135, c_64666])).
% 25.56/16.11  tff(c_65331, plain, (![A_638, B_639]: (k3_xboole_0(A_638, B_639)=B_639 | ~r1_tarski(B_639, k3_xboole_0(A_638, B_639)))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_64720])).
% 25.56/16.11  tff(c_65376, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(B_4, k3_xboole_0(B_4, A_3)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_65331])).
% 25.56/16.11  tff(c_72163, plain, (k3_xboole_0('#skF_4', '#skF_2')='#skF_2' | ~r1_tarski('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_72132, c_65376])).
% 25.56/16.11  tff(c_72254, plain, (k3_xboole_0('#skF_4', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_72163])).
% 25.56/16.11  tff(c_64571, plain, (![C_620, B_621, A_622]: (r1_tarski(k2_zfmisc_1(C_620, B_621), k2_zfmisc_1(C_620, k2_xboole_0(A_622, B_621))))), inference(superposition, [status(thm), theory('equality')], [c_61757, c_69])).
% 25.56/16.11  tff(c_65609, plain, (![C_647, A_648, B_649]: (r1_tarski(k2_zfmisc_1(C_647, k3_xboole_0(A_648, B_649)), k2_zfmisc_1(C_647, B_649)))), inference(superposition, [status(thm), theory('equality')], [c_135, c_64571])).
% 25.56/16.11  tff(c_65668, plain, (![A_648]: (r1_tarski(k2_zfmisc_1('#skF_3', k3_xboole_0(A_648, '#skF_4')), k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_36, c_65609])).
% 25.56/16.11  tff(c_72165, plain, (r1_tarski(k2_zfmisc_1('#skF_3', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_72132, c_65668])).
% 25.56/16.11  tff(c_22, plain, (![B_16, A_15, C_17]: (~r1_tarski(k2_zfmisc_1(B_16, A_15), k2_zfmisc_1(C_17, A_15)) | r1_tarski(B_16, C_17) | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_58])).
% 25.56/16.11  tff(c_63211, plain, (![B_16, A_15, C_17]: (~r1_tarski(k2_zfmisc_1(B_16, A_15), k2_zfmisc_1(C_17, A_15)) | r1_tarski(B_16, C_17) | A_15='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_63210, c_22])).
% 25.56/16.11  tff(c_73036, plain, (r1_tarski('#skF_3', '#skF_1') | '#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_72165, c_63211])).
% 25.56/16.11  tff(c_73050, plain, (r1_tarski('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_63214, c_73036])).
% 25.56/16.11  tff(c_73068, plain, (k3_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_73050, c_16])).
% 25.56/16.11  tff(c_73927, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_4, c_73068])).
% 25.56/16.11  tff(c_63065, plain, (![A_588, C_589]: (k3_xboole_0(k2_zfmisc_1(A_588, C_589), k2_zfmisc_1('#skF_1', '#skF_2'))=k2_zfmisc_1(k3_xboole_0(A_588, '#skF_3'), k3_xboole_0(C_589, '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_36, c_62994])).
% 25.56/16.11  tff(c_66758, plain, (![A_666, C_667]: (k2_zfmisc_1(k3_xboole_0(A_666, '#skF_3'), k3_xboole_0(C_667, '#skF_4'))=k2_zfmisc_1(k3_xboole_0(A_666, '#skF_1'), k3_xboole_0(C_667, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_63065])).
% 25.56/16.11  tff(c_66894, plain, (![C_667]: (k2_zfmisc_1(k3_xboole_0('#skF_3', '#skF_1'), k3_xboole_0(C_667, '#skF_2'))=k2_zfmisc_1('#skF_3', k3_xboole_0(C_667, '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_186, c_66758])).
% 25.56/16.11  tff(c_66931, plain, (![C_667]: (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0(C_667, '#skF_2'))=k2_zfmisc_1('#skF_3', k3_xboole_0(C_667, '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_66894])).
% 25.56/16.11  tff(c_75523, plain, (![C_727]: (k2_zfmisc_1('#skF_3', k3_xboole_0(C_727, '#skF_2'))=k2_zfmisc_1('#skF_3', k3_xboole_0(C_727, '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_73927, c_66931])).
% 25.56/16.11  tff(c_75659, plain, (k2_zfmisc_1('#skF_3', k3_xboole_0('#skF_4', '#skF_4'))=k2_zfmisc_1('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_72254, c_75523])).
% 25.56/16.11  tff(c_75723, plain, (k2_zfmisc_1('#skF_3', '#skF_2')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_186, c_75659])).
% 25.56/16.11  tff(c_2463, plain, (![A_102]: (k2_xboole_0(k2_zfmisc_1(A_102, '#skF_4'), k2_zfmisc_1('#skF_1', '#skF_2'))=k2_zfmisc_1(k2_xboole_0(A_102, '#skF_3'), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_874])).
% 25.56/16.11  tff(c_2476, plain, (k2_zfmisc_1(k2_xboole_0('#skF_1', '#skF_3'), '#skF_4')=k2_zfmisc_1('#skF_1', k2_xboole_0('#skF_4', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2463, c_26])).
% 25.56/16.11  tff(c_1261, plain, (![A_78, B_79]: (k3_xboole_0(k3_xboole_0(A_78, B_79), B_79)=k3_xboole_0(A_78, B_79))), inference(superposition, [status(thm), theory('equality')], [c_135, c_328])).
% 25.56/16.11  tff(c_2316, plain, (![A_100, B_101]: (k3_xboole_0(k3_xboole_0(A_100, B_101), A_100)=k3_xboole_0(B_101, A_100))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1261])).
% 25.56/16.11  tff(c_2413, plain, (![A_1, B_2]: (k3_xboole_0(k2_xboole_0(A_1, B_2), B_2)=k3_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_248, c_2316])).
% 25.56/16.11  tff(c_2458, plain, (![A_1, B_2]: (k3_xboole_0(k2_xboole_0(A_1, B_2), B_2)=B_2)), inference(demodulation, [status(thm), theory('equality')], [c_186, c_2413])).
% 25.56/16.11  tff(c_2851, plain, (![A_107, C_108, B_109, D_110]: (k3_xboole_0(k2_zfmisc_1(A_107, C_108), k2_zfmisc_1(B_109, D_110))=k2_zfmisc_1(k3_xboole_0(A_107, B_109), k3_xboole_0(C_108, D_110)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 25.56/16.11  tff(c_2897, plain, (![B_109, D_110, A_107, C_108]: (k3_xboole_0(k2_zfmisc_1(B_109, D_110), k2_zfmisc_1(A_107, C_108))=k2_zfmisc_1(k3_xboole_0(A_107, B_109), k3_xboole_0(C_108, D_110)))), inference(superposition, [status(thm), theory('equality')], [c_2851, c_4])).
% 25.56/16.11  tff(c_663, plain, (![A_1, B_2]: (k2_xboole_0(k2_xboole_0(A_1, B_2), B_2)=k2_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_605])).
% 25.56/16.11  tff(c_57124, plain, (![A_537]: (k3_xboole_0(k2_zfmisc_1(A_537, '#skF_4'), k2_zfmisc_1(k2_xboole_0(A_537, '#skF_3'), '#skF_4'))=k2_zfmisc_1(A_537, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2463, c_185])).
% 25.56/16.11  tff(c_57251, plain, (k3_xboole_0(k2_zfmisc_1('#skF_1', k2_xboole_0('#skF_4', '#skF_2')), k2_zfmisc_1(k2_xboole_0(k2_xboole_0('#skF_1', '#skF_3'), '#skF_3'), '#skF_4'))=k2_zfmisc_1(k2_xboole_0('#skF_1', '#skF_3'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2476, c_57124])).
% 25.56/16.11  tff(c_57336, plain, (k2_zfmisc_1('#skF_1', k2_xboole_0('#skF_4', '#skF_2'))=k2_zfmisc_1('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2476, c_185, c_2458, c_2897, c_663, c_57251])).
% 25.56/16.11  tff(c_1491, plain, (![C_82, A_83, B_84]: (k2_xboole_0(k2_zfmisc_1(C_82, A_83), k2_zfmisc_1(C_82, B_84))=k2_zfmisc_1(C_82, k2_xboole_0(A_83, B_84)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 25.56/16.11  tff(c_3041, plain, (![C_112, A_113, B_114]: (r1_tarski(k2_zfmisc_1(C_112, A_113), k2_zfmisc_1(C_112, k2_xboole_0(A_113, B_114))))), inference(superposition, [status(thm), theory('equality')], [c_1491, c_18])).
% 25.56/16.11  tff(c_3106, plain, (![C_112, B_2, A_1]: (r1_tarski(k2_zfmisc_1(C_112, B_2), k2_zfmisc_1(C_112, k2_xboole_0(A_1, B_2))))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3041])).
% 25.56/16.11  tff(c_57395, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_57336, c_3106])).
% 25.56/16.11  tff(c_532, plain, (![A_58, B_59, C_60]: (~r1_tarski(k2_zfmisc_1(A_58, B_59), k2_zfmisc_1(A_58, C_60)) | r1_tarski(B_59, C_60) | k1_xboole_0=A_58)), inference(cnfTransformation, [status(thm)], [f_58])).
% 25.56/16.11  tff(c_538, plain, (![B_59]: (~r1_tarski(k2_zfmisc_1('#skF_3', B_59), k2_zfmisc_1('#skF_1', '#skF_2')) | r1_tarski(B_59, '#skF_4') | k1_xboole_0='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_532])).
% 25.56/16.11  tff(c_1123, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_538])).
% 25.56/16.11  tff(c_2193, plain, (![B_95, A_96, C_97]: (~r1_tarski(k2_zfmisc_1(B_95, A_96), k2_zfmisc_1(C_97, A_96)) | r1_tarski(B_95, C_97) | A_96='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1123, c_22])).
% 25.56/16.11  tff(c_2196, plain, (![C_97]: (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1(C_97, '#skF_4')) | r1_tarski('#skF_3', C_97) | '#skF_3'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_36, c_2193])).
% 25.56/16.11  tff(c_6750, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_2196])).
% 25.56/16.11  tff(c_6772, plain, ('#skF_1'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6750, c_39])).
% 25.56/16.11  tff(c_6771, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k2_zfmisc_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6750, c_36])).
% 25.56/16.11  tff(c_2943, plain, (![B_111]: (k2_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1(B_111, '#skF_4'))=k2_zfmisc_1(k2_xboole_0('#skF_3', B_111), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_874])).
% 25.56/16.11  tff(c_2992, plain, (![B_111]: (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1(k2_xboole_0('#skF_3', B_111), '#skF_4'))=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2943, c_185])).
% 25.56/16.11  tff(c_15133, plain, (![B_250]: (k2_zfmisc_1(k3_xboole_0('#skF_1', k2_xboole_0('#skF_4', B_250)), k3_xboole_0('#skF_4', '#skF_2'))=k2_zfmisc_1('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6771, c_4, c_28, c_6750, c_2992])).
% 25.56/16.11  tff(c_6235, plain, (![A_179, C_180, B_181, D_182]: (k2_xboole_0(k2_zfmisc_1(A_179, C_180), k2_zfmisc_1(k3_xboole_0(A_179, B_181), k3_xboole_0(C_180, D_182)))=k2_zfmisc_1(A_179, C_180))), inference(superposition, [status(thm), theory('equality')], [c_2851, c_14])).
% 25.56/16.11  tff(c_6307, plain, (![A_179, B_181, C_180, D_182]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_179, B_181), k3_xboole_0(C_180, D_182)), k2_zfmisc_1(A_179, C_180)))), inference(superposition, [status(thm), theory('equality')], [c_6235, c_69])).
% 25.56/16.11  tff(c_15159, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_4'), k2_zfmisc_1('#skF_1', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_15133, c_6307])).
% 25.56/16.11  tff(c_1124, plain, (![A_15, B_16, C_17]: (~r1_tarski(k2_zfmisc_1(A_15, B_16), k2_zfmisc_1(A_15, C_17)) | r1_tarski(B_16, C_17) | A_15='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1123, c_20])).
% 25.56/16.11  tff(c_17375, plain, (![A_254, B_255, C_256]: (~r1_tarski(k2_zfmisc_1(A_254, B_255), k2_zfmisc_1(A_254, C_256)) | r1_tarski(B_255, C_256) | A_254='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6750, c_1124])).
% 25.56/16.11  tff(c_17477, plain, (![C_256]: (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_4'), k2_zfmisc_1('#skF_1', C_256)) | r1_tarski('#skF_2', C_256) | '#skF_1'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6771, c_17375])).
% 25.56/16.11  tff(c_17519, plain, (![C_257]: (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_4'), k2_zfmisc_1('#skF_1', C_257)) | r1_tarski('#skF_2', C_257))), inference(negUnitSimplification, [status(thm)], [c_6772, c_17477])).
% 25.56/16.11  tff(c_17550, plain, (r1_tarski('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_15159, c_17519])).
% 25.56/16.11  tff(c_17569, plain, (k3_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(resolution, [status(thm)], [c_17550, c_16])).
% 25.56/16.11  tff(c_4422, plain, (![C_140, B_141, A_142]: (r1_tarski(k2_zfmisc_1(C_140, B_141), k2_zfmisc_1(C_140, k2_xboole_0(A_142, B_141))))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3041])).
% 25.56/16.11  tff(c_4484, plain, (![C_140, A_37, B_36]: (r1_tarski(k2_zfmisc_1(C_140, k3_xboole_0(A_37, B_36)), k2_zfmisc_1(C_140, B_36)))), inference(superposition, [status(thm), theory('equality')], [c_135, c_4422])).
% 25.56/16.11  tff(c_17836, plain, (![C_140]: (r1_tarski(k2_zfmisc_1(C_140, '#skF_2'), k2_zfmisc_1(C_140, '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_17569, c_4484])).
% 25.56/16.11  tff(c_1125, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1123, c_32])).
% 25.56/16.11  tff(c_6769, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6750, c_1125])).
% 25.56/16.11  tff(c_2192, plain, (![B_16, A_15, C_17]: (~r1_tarski(k2_zfmisc_1(B_16, A_15), k2_zfmisc_1(C_17, A_15)) | r1_tarski(B_16, C_17) | A_15='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1123, c_22])).
% 25.56/16.11  tff(c_18298, plain, (![B_258, A_259, C_260]: (~r1_tarski(k2_zfmisc_1(B_258, A_259), k2_zfmisc_1(C_260, A_259)) | r1_tarski(B_258, C_260) | A_259='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6750, c_2192])).
% 25.56/16.11  tff(c_18373, plain, (![B_258]: (~r1_tarski(k2_zfmisc_1(B_258, '#skF_2'), k2_zfmisc_1('#skF_4', '#skF_4')) | r1_tarski(B_258, '#skF_1') | '#skF_2'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6771, c_18298])).
% 25.56/16.11  tff(c_23724, plain, (![B_335]: (~r1_tarski(k2_zfmisc_1(B_335, '#skF_2'), k2_zfmisc_1('#skF_4', '#skF_4')) | r1_tarski(B_335, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_6769, c_18373])).
% 25.56/16.11  tff(c_23777, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_17836, c_23724])).
% 25.56/16.11  tff(c_23793, plain, ('#skF_1'='#skF_4' | ~r1_tarski('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_23777, c_6])).
% 25.56/16.11  tff(c_23802, plain, (~r1_tarski('#skF_1', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_6772, c_23793])).
% 25.56/16.11  tff(c_12, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 25.56/16.11  tff(c_17568, plain, (k2_xboole_0('#skF_2', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_17550, c_12])).
% 25.56/16.11  tff(c_17718, plain, (k2_xboole_0('#skF_4', '#skF_2')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2, c_17568])).
% 25.56/16.11  tff(c_3568, plain, (![B_122]: (k2_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', B_122))=k2_zfmisc_1('#skF_3', k2_xboole_0('#skF_4', B_122)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1491])).
% 25.56/16.11  tff(c_3627, plain, (![B_122]: (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', k2_xboole_0('#skF_4', B_122)))=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3568, c_185])).
% 25.56/16.11  tff(c_14529, plain, (![B_249]: (k2_zfmisc_1(k3_xboole_0('#skF_4', '#skF_1'), k3_xboole_0('#skF_2', k2_xboole_0('#skF_4', B_249)))=k2_zfmisc_1('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6771, c_4, c_28, c_6750, c_3627])).
% 25.56/16.11  tff(c_2906, plain, (![A_107, C_108, B_109, D_110]: (k2_xboole_0(k2_zfmisc_1(A_107, C_108), k2_zfmisc_1(k3_xboole_0(A_107, B_109), k3_xboole_0(C_108, D_110)))=k2_zfmisc_1(A_107, C_108))), inference(superposition, [status(thm), theory('equality')], [c_2851, c_14])).
% 25.56/16.11  tff(c_14570, plain, (k2_xboole_0(k2_zfmisc_1('#skF_4', '#skF_2'), k2_zfmisc_1('#skF_4', '#skF_4'))=k2_zfmisc_1('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_14529, c_2906])).
% 25.56/16.11  tff(c_259, plain, (![A_46, B_47]: (k2_xboole_0(A_46, B_47)=B_47 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_39])).
% 25.56/16.11  tff(c_546, plain, (![A_61, B_62]: (k2_xboole_0(A_61, k2_xboole_0(A_61, B_62))=k2_xboole_0(A_61, B_62))), inference(resolution, [status(thm)], [c_18, c_259])).
% 25.56/16.11  tff(c_775, plain, (![A_67, B_68]: (k2_xboole_0(A_67, k2_xboole_0(B_68, A_67))=k2_xboole_0(A_67, B_68))), inference(superposition, [status(thm), theory('equality')], [c_2, c_546])).
% 25.56/16.11  tff(c_800, plain, (![B_68, A_67]: (k3_xboole_0(k2_xboole_0(B_68, A_67), k2_xboole_0(A_67, B_68))=k2_xboole_0(B_68, A_67))), inference(superposition, [status(thm), theory('equality')], [c_775, c_248])).
% 25.56/16.11  tff(c_14864, plain, (k3_xboole_0(k2_zfmisc_1('#skF_4', '#skF_2'), k2_xboole_0(k2_zfmisc_1('#skF_4', '#skF_4'), k2_zfmisc_1('#skF_4', '#skF_2')))=k2_xboole_0(k2_zfmisc_1('#skF_4', '#skF_2'), k2_zfmisc_1('#skF_4', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_14570, c_800])).
% 25.56/16.11  tff(c_14990, plain, (k2_zfmisc_1('#skF_4', k2_xboole_0('#skF_4', '#skF_2'))=k2_zfmisc_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_248, c_2, c_14864])).
% 25.56/16.11  tff(c_17945, plain, (k2_zfmisc_1('#skF_4', '#skF_2')=k2_zfmisc_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_17718, c_14990])).
% 25.56/16.11  tff(c_18370, plain, (![C_260]: (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_4'), k2_zfmisc_1(C_260, '#skF_2')) | r1_tarski('#skF_1', C_260) | '#skF_2'='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6771, c_18298])).
% 25.56/16.11  tff(c_51448, plain, (![C_497]: (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_4'), k2_zfmisc_1(C_497, '#skF_2')) | r1_tarski('#skF_1', C_497))), inference(negUnitSimplification, [status(thm)], [c_6769, c_18370])).
% 25.56/16.11  tff(c_51468, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_4'), k2_zfmisc_1('#skF_4', '#skF_4')) | r1_tarski('#skF_1', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_17945, c_51448])).
% 25.56/16.11  tff(c_51494, plain, (r1_tarski('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_51468])).
% 25.56/16.11  tff(c_51496, plain, $false, inference(negUnitSimplification, [status(thm)], [c_23802, c_51494])).
% 25.56/16.11  tff(c_51497, plain, (![C_97]: (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1(C_97, '#skF_4')) | r1_tarski('#skF_3', C_97))), inference(splitRight, [status(thm)], [c_2196])).
% 25.56/16.11  tff(c_57476, plain, (r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_57395, c_51497])).
% 25.56/16.11  tff(c_57484, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_57476, c_6])).
% 25.56/16.11  tff(c_57493, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_39, c_57484])).
% 25.56/16.11  tff(c_57495, plain, (k3_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_57476, c_16])).
% 25.56/16.11  tff(c_58558, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_4, c_57495])).
% 25.56/16.11  tff(c_57467, plain, (r1_tarski('#skF_2', '#skF_4') | '#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_57395, c_1124])).
% 25.56/16.11  tff(c_57479, plain, (r1_tarski('#skF_2', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_39, c_57467])).
% 25.56/16.11  tff(c_57505, plain, (k2_xboole_0('#skF_2', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_57479, c_12])).
% 25.56/16.11  tff(c_2416, plain, (![A_13, B_14]: (k3_xboole_0(k2_xboole_0(A_13, B_14), A_13)=k3_xboole_0(A_13, A_13))), inference(superposition, [status(thm), theory('equality')], [c_185, c_2316])).
% 25.56/16.11  tff(c_2459, plain, (![A_13, B_14]: (k3_xboole_0(k2_xboole_0(A_13, B_14), A_13)=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_186, c_2416])).
% 25.56/16.11  tff(c_58226, plain, (k3_xboole_0('#skF_4', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_57505, c_2459])).
% 25.56/16.11  tff(c_2922, plain, (![B_109, D_110]: (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1(B_109, D_110))=k2_zfmisc_1(k3_xboole_0('#skF_3', B_109), k3_xboole_0('#skF_4', D_110)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_2851])).
% 25.56/16.11  tff(c_52161, plain, (![B_502, D_503]: (k2_zfmisc_1(k3_xboole_0('#skF_3', B_502), k3_xboole_0('#skF_4', D_503))=k2_zfmisc_1(k3_xboole_0('#skF_1', B_502), k3_xboole_0('#skF_2', D_503)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2922])).
% 25.56/16.11  tff(c_52313, plain, (![B_502]: (k2_zfmisc_1(k3_xboole_0('#skF_1', B_502), k3_xboole_0('#skF_2', '#skF_4'))=k2_zfmisc_1(k3_xboole_0('#skF_3', B_502), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_186, c_52161])).
% 25.56/16.11  tff(c_52342, plain, (![B_502]: (k2_zfmisc_1(k3_xboole_0('#skF_1', B_502), k3_xboole_0('#skF_4', '#skF_2'))=k2_zfmisc_1(k3_xboole_0('#skF_3', B_502), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_52313])).
% 25.56/16.11  tff(c_59239, plain, (![B_542]: (k2_zfmisc_1(k3_xboole_0('#skF_3', B_542), '#skF_4')=k2_zfmisc_1(k3_xboole_0('#skF_1', B_542), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58226, c_52342])).
% 25.56/16.11  tff(c_59391, plain, (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k2_zfmisc_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_186, c_59239])).
% 25.56/16.11  tff(c_59426, plain, (k2_zfmisc_1('#skF_3', '#skF_2')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58558, c_36, c_59391])).
% 25.56/16.11  tff(c_60615, plain, (![B_16]: (~r1_tarski(k2_zfmisc_1(B_16, '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')) | r1_tarski(B_16, '#skF_3') | '#skF_2'='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_59426, c_2192])).
% 25.56/16.11  tff(c_61362, plain, (![B_557]: (~r1_tarski(k2_zfmisc_1(B_557, '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')) | r1_tarski(B_557, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_1125, c_60615])).
% 25.56/16.11  tff(c_61385, plain, (r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_10, c_61362])).
% 25.56/16.11  tff(c_61393, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57493, c_61385])).
% 25.56/16.11  tff(c_61395, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_538])).
% 25.56/16.11  tff(c_535, plain, (![C_60]: (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', C_60)) | r1_tarski('#skF_4', C_60) | k1_xboole_0='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_532])).
% 25.56/16.11  tff(c_62553, plain, (![C_60]: (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', C_60)) | r1_tarski('#skF_4', C_60))), inference(negUnitSimplification, [status(thm)], [c_61395, c_535])).
% 25.56/16.11  tff(c_75953, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')) | r1_tarski('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_75723, c_62553])).
% 25.56/16.11  tff(c_75998, plain, (r1_tarski('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_75953])).
% 25.56/16.11  tff(c_76000, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72130, c_75998])).
% 25.56/16.11  tff(c_76001, plain, (![C_578]: (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1(C_578, '#skF_4')) | r1_tarski('#skF_3', C_578))), inference(splitRight, [status(thm)], [c_62423])).
% 25.56/16.11  tff(c_82439, plain, (r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_82370, c_76001])).
% 25.56/16.11  tff(c_82458, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_82439, c_6])).
% 25.56/16.11  tff(c_82467, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_39, c_82458])).
% 25.56/16.11  tff(c_82430, plain, (r1_tarski('#skF_2', '#skF_4') | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_82370, c_20])).
% 25.56/16.11  tff(c_82442, plain, (r1_tarski('#skF_2', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_34, c_82430])).
% 25.56/16.11  tff(c_82454, plain, ('#skF_2'='#skF_4' | ~r1_tarski('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_82442, c_6])).
% 25.56/16.11  tff(c_83777, plain, (~r1_tarski('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_82454])).
% 25.56/16.11  tff(c_82468, plain, (k2_xboole_0('#skF_3', '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_82439, c_12])).
% 25.56/16.11  tff(c_83132, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_82468, c_62159])).
% 25.56/16.11  tff(c_82455, plain, (k2_xboole_0('#skF_2', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_82442, c_12])).
% 25.56/16.11  tff(c_82706, plain, (k3_xboole_0('#skF_4', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_82455, c_62159])).
% 25.56/16.11  tff(c_187, plain, (![B_42]: (k3_xboole_0(B_42, B_42)=B_42)), inference(resolution, [status(thm)], [c_10, c_166])).
% 25.56/16.11  tff(c_199, plain, (![B_42]: (k2_xboole_0(B_42, B_42)=B_42)), inference(superposition, [status(thm), theory('equality')], [c_187, c_14])).
% 25.56/16.11  tff(c_82281, plain, (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_3'), '#skF_4'))=k2_zfmisc_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_36, c_82130])).
% 25.56/16.11  tff(c_82326, plain, (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_4', '#skF_2'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_4, c_28, c_199, c_82281])).
% 25.56/16.11  tff(c_85026, plain, (k2_zfmisc_1('#skF_3', '#skF_2')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_83132, c_82706, c_82326])).
% 25.56/16.11  tff(c_85111, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_1', '#skF_2')) | r1_tarski('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_85026, c_62553])).
% 25.56/16.11  tff(c_85161, plain, (r1_tarski('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_85111])).
% 25.56/16.11  tff(c_85163, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83777, c_85161])).
% 25.56/16.11  tff(c_85164, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_82454])).
% 25.56/16.11  tff(c_76002, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_62423])).
% 25.56/16.11  tff(c_62426, plain, (![B_576]: (~r1_tarski(k2_zfmisc_1(B_576, '#skF_4'), k2_zfmisc_1('#skF_1', '#skF_2')) | r1_tarski(B_576, '#skF_3') | k1_xboole_0='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_36, c_62420])).
% 25.56/16.11  tff(c_78784, plain, (![B_576]: (~r1_tarski(k2_zfmisc_1(B_576, '#skF_4'), k2_zfmisc_1('#skF_1', '#skF_2')) | r1_tarski(B_576, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_76002, c_62426])).
% 25.56/16.11  tff(c_107417, plain, (![B_1022]: (~r1_tarski(k2_zfmisc_1(B_1022, '#skF_4'), k2_zfmisc_1('#skF_1', '#skF_4')) | r1_tarski(B_1022, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_85164, c_78784])).
% 25.56/16.11  tff(c_107481, plain, (r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_10, c_107417])).
% 25.56/16.11  tff(c_107503, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82467, c_107481])).
% 25.56/16.11  tff(c_107504, plain, ('#skF_2'!='#skF_4'), inference(splitRight, [status(thm)], [c_30])).
% 25.56/16.11  tff(c_107505, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_30])).
% 25.56/16.11  tff(c_107550, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k2_zfmisc_1('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_107505, c_36])).
% 25.56/16.11  tff(c_108873, plain, (![A_1078, B_1079, C_1080]: (~r1_tarski(k2_zfmisc_1(A_1078, B_1079), k2_zfmisc_1(A_1078, C_1080)) | r1_tarski(B_1079, C_1080) | k1_xboole_0=A_1078)), inference(cnfTransformation, [status(thm)], [f_58])).
% 25.56/16.11  tff(c_108879, plain, (![B_1079]: (~r1_tarski(k2_zfmisc_1('#skF_1', B_1079), k2_zfmisc_1('#skF_1', '#skF_4')) | r1_tarski(B_1079, '#skF_2') | k1_xboole_0='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_107550, c_108873])).
% 25.56/16.11  tff(c_109925, plain, (![B_1101]: (~r1_tarski(k2_zfmisc_1('#skF_1', B_1101), k2_zfmisc_1('#skF_1', '#skF_4')) | r1_tarski(B_1101, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_34, c_108879])).
% 25.56/16.11  tff(c_109935, plain, (r1_tarski('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_10, c_109925])).
% 25.56/16.11  tff(c_109937, plain, ('#skF_2'='#skF_4' | ~r1_tarski('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_109935, c_6])).
% 25.56/16.11  tff(c_109946, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_107504, c_109937])).
% 25.56/16.11  tff(c_108876, plain, (![C_1080]: (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_1', C_1080)) | r1_tarski('#skF_2', C_1080) | k1_xboole_0='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_107550, c_108873])).
% 25.56/16.11  tff(c_110304, plain, (![C_1106]: (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_1', C_1106)) | r1_tarski('#skF_2', C_1106))), inference(negUnitSimplification, [status(thm)], [c_34, c_108876])).
% 25.56/16.11  tff(c_110311, plain, (r1_tarski('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_10, c_110304])).
% 25.56/16.11  tff(c_110317, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109946, c_110311])).
% 25.56/16.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.56/16.11  
% 25.56/16.11  Inference rules
% 25.56/16.11  ----------------------
% 25.56/16.11  #Ref     : 0
% 25.56/16.11  #Sup     : 28317
% 25.56/16.11  #Fact    : 0
% 25.56/16.11  #Define  : 0
% 25.56/16.11  #Split   : 7
% 25.56/16.11  #Chain   : 0
% 25.56/16.11  #Close   : 0
% 25.56/16.11  
% 25.56/16.11  Ordering : KBO
% 25.56/16.11  
% 25.56/16.11  Simplification rules
% 25.56/16.11  ----------------------
% 25.56/16.11  #Subsume      : 2011
% 25.56/16.11  #Demod        : 33773
% 25.56/16.11  #Tautology    : 14828
% 25.56/16.11  #SimpNegUnit  : 157
% 25.56/16.11  #BackRed      : 93
% 25.56/16.11  
% 25.56/16.11  #Partial instantiations: 0
% 25.56/16.11  #Strategies tried      : 1
% 25.56/16.11  
% 25.56/16.11  Timing (in seconds)
% 25.56/16.11  ----------------------
% 25.56/16.11  Preprocessing        : 0.29
% 25.56/16.11  Parsing              : 0.15
% 25.56/16.11  CNF conversion       : 0.02
% 25.56/16.11  Main loop            : 15.03
% 25.56/16.11  Inferencing          : 2.03
% 25.56/16.11  Reduction            : 9.47
% 25.56/16.11  Demodulation         : 8.70
% 25.56/16.11  BG Simplification    : 0.30
% 25.56/16.11  Subsumption          : 2.44
% 25.56/16.11  Abstraction          : 0.54
% 25.56/16.11  MUC search           : 0.00
% 25.56/16.11  Cooper               : 0.00
% 25.56/16.11  Total                : 15.40
% 25.56/16.11  Index Insertion      : 0.00
% 25.56/16.11  Index Deletion       : 0.00
% 25.56/16.11  Index Matching       : 0.00
% 25.56/16.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
