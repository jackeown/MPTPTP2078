%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:14 EST 2020

% Result     : Theorem 42.52s
% Output     : CNFRefutation 42.86s
% Verified   : 
% Statistics : Number of formulae       :  223 ( 892 expanded)
%              Number of leaves         :   39 ( 313 expanded)
%              Depth                    :   20
%              Number of atoms          :  329 (1672 expanded)
%              Number of equality atoms :  156 ( 789 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_13 > #skF_5 > #skF_8 > #skF_3 > #skF_2 > #skF_7 > #skF_9 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_116,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_97,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_90,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_103,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_86,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_105,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_76,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(c_94,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_64,plain,(
    ! [B_30] : r1_tarski(B_30,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_92,plain,
    ( '#skF_11' != '#skF_13'
    | '#skF_10' != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_102,plain,(
    '#skF_10' != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_2'(A_7,B_8),A_7)
      | r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_74,plain,(
    ! [C_39] : r2_hidden(C_39,k1_tarski(C_39)) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_70,plain,(
    ! [A_34] : k4_xboole_0(k1_xboole_0,A_34) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_300,plain,(
    ! [D_68,B_69,A_70] :
      ( ~ r2_hidden(D_68,B_69)
      | ~ r2_hidden(D_68,k4_xboole_0(A_70,B_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_309,plain,(
    ! [D_71,A_72] :
      ( ~ r2_hidden(D_71,A_72)
      | ~ r2_hidden(D_71,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_300])).

tff(c_316,plain,(
    ! [C_73] : ~ r2_hidden(C_73,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_74,c_309])).

tff(c_321,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_316])).

tff(c_88,plain,(
    ! [B_41] : k2_zfmisc_1(k1_xboole_0,B_41) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_315,plain,(
    ! [C_39] : ~ r2_hidden(C_39,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_74,c_309])).

tff(c_3813,plain,(
    ! [A_3111,B_3112,C_3113] :
      ( r2_hidden('#skF_3'(A_3111,B_3112,C_3113),A_3111)
      | r2_hidden('#skF_4'(A_3111,B_3112,C_3113),C_3113)
      | k3_xboole_0(A_3111,B_3112) = C_3113 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3883,plain,(
    ! [A_3111,B_3112] :
      ( r2_hidden('#skF_3'(A_3111,B_3112,k1_xboole_0),A_3111)
      | k3_xboole_0(A_3111,B_3112) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3813,c_315])).

tff(c_4384,plain,(
    ! [A_3354,B_3355,C_3356] :
      ( r2_hidden('#skF_3'(A_3354,B_3355,C_3356),B_3355)
      | r2_hidden('#skF_4'(A_3354,B_3355,C_3356),C_3356)
      | k3_xboole_0(A_3354,B_3355) = C_3356 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_34,plain,(
    ! [D_23,B_19,A_18] :
      ( ~ r2_hidden(D_23,B_19)
      | ~ r2_hidden(D_23,k4_xboole_0(A_18,B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_88545,plain,(
    ! [A_15292,A_15293,B_15294,C_15295] :
      ( ~ r2_hidden('#skF_3'(A_15292,k4_xboole_0(A_15293,B_15294),C_15295),B_15294)
      | r2_hidden('#skF_4'(A_15292,k4_xboole_0(A_15293,B_15294),C_15295),C_15295)
      | k3_xboole_0(A_15292,k4_xboole_0(A_15293,B_15294)) = C_15295 ) ),
    inference(resolution,[status(thm)],[c_4384,c_34])).

tff(c_88617,plain,(
    ! [A_3111,A_15293] :
      ( r2_hidden('#skF_4'(A_3111,k4_xboole_0(A_15293,A_3111),k1_xboole_0),k1_xboole_0)
      | k3_xboole_0(A_3111,k4_xboole_0(A_15293,A_3111)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3883,c_88545])).

tff(c_88664,plain,(
    ! [A_15324,A_15325] : k3_xboole_0(A_15324,k4_xboole_0(A_15325,A_15324)) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_315,c_88617])).

tff(c_266,plain,(
    ! [A_65,B_66] :
      ( k3_xboole_0(A_65,B_66) = A_65
      | ~ r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_270,plain,(
    ! [B_30] : k3_xboole_0(B_30,B_30) = B_30 ),
    inference(resolution,[status(thm)],[c_64,c_266])).

tff(c_90,plain,(
    ! [A_42,C_44,B_43,D_45] : k3_xboole_0(k2_zfmisc_1(A_42,C_44),k2_zfmisc_1(B_43,D_45)) = k2_zfmisc_1(k3_xboole_0(A_42,B_43),k3_xboole_0(C_44,D_45)) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_98,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') = k2_zfmisc_1('#skF_12','#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1990,plain,(
    ! [A_2255,C_2256,B_2257,D_2258] : k3_xboole_0(k2_zfmisc_1(A_2255,C_2256),k2_zfmisc_1(B_2257,D_2258)) = k2_zfmisc_1(k3_xboole_0(A_2255,B_2257),k3_xboole_0(C_2256,D_2258)) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2048,plain,(
    ! [B_2257,D_2258] : k3_xboole_0(k2_zfmisc_1('#skF_12','#skF_13'),k2_zfmisc_1(B_2257,D_2258)) = k2_zfmisc_1(k3_xboole_0('#skF_10',B_2257),k3_xboole_0('#skF_11',D_2258)) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_1990])).

tff(c_3176,plain,(
    ! [B_2840,D_2841] : k2_zfmisc_1(k3_xboole_0('#skF_10',B_2840),k3_xboole_0('#skF_11',D_2841)) = k2_zfmisc_1(k3_xboole_0('#skF_12',B_2840),k3_xboole_0('#skF_13',D_2841)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_2048])).

tff(c_3234,plain,(
    ! [B_2840] : k2_zfmisc_1(k3_xboole_0('#skF_12',B_2840),k3_xboole_0('#skF_13','#skF_11')) = k2_zfmisc_1(k3_xboole_0('#skF_10',B_2840),'#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_3176])).

tff(c_89453,plain,(
    ! [A_15325] : k2_zfmisc_1(k3_xboole_0('#skF_10',k4_xboole_0(A_15325,'#skF_12')),'#skF_11') = k2_zfmisc_1(k1_xboole_0,k3_xboole_0('#skF_13','#skF_11')) ),
    inference(superposition,[status(thm),theory(equality)],[c_88664,c_3234])).

tff(c_91498,plain,(
    ! [A_15414] : k2_zfmisc_1(k3_xboole_0('#skF_10',k4_xboole_0(A_15414,'#skF_12')),'#skF_11') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_89453])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4645,plain,(
    ! [A_3475,D_3476] : k2_zfmisc_1(k3_xboole_0(A_3475,'#skF_10'),k3_xboole_0('#skF_11',D_3476)) = k2_zfmisc_1(k3_xboole_0('#skF_12',A_3475),k3_xboole_0('#skF_13',D_3476)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3176])).

tff(c_4690,plain,(
    ! [B_2840] : k2_zfmisc_1(k3_xboole_0(B_2840,'#skF_10'),k3_xboole_0('#skF_11','#skF_11')) = k2_zfmisc_1(k3_xboole_0('#skF_10',B_2840),'#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_3234,c_4645])).

tff(c_5043,plain,(
    ! [B_3681] : k2_zfmisc_1(k3_xboole_0(B_3681,'#skF_10'),'#skF_11') = k2_zfmisc_1(k3_xboole_0('#skF_10',B_3681),'#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_4690])).

tff(c_84,plain,(
    ! [B_41,A_40] :
      ( k1_xboole_0 = B_41
      | k1_xboole_0 = A_40
      | k2_zfmisc_1(A_40,B_41) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_5064,plain,(
    ! [B_3681] :
      ( k1_xboole_0 = '#skF_11'
      | k3_xboole_0('#skF_10',B_3681) = k1_xboole_0
      | k2_zfmisc_1(k3_xboole_0(B_3681,'#skF_10'),'#skF_11') != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5043,c_84])).

tff(c_5740,plain,(
    ! [B_3892] :
      ( k3_xboole_0('#skF_10',B_3892) = k1_xboole_0
      | k2_zfmisc_1(k3_xboole_0(B_3892,'#skF_10'),'#skF_11') != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_5064])).

tff(c_5784,plain,(
    ! [B_2] :
      ( k3_xboole_0('#skF_10',B_2) = k1_xboole_0
      | k2_zfmisc_1(k3_xboole_0('#skF_10',B_2),'#skF_11') != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_5740])).

tff(c_91664,plain,(
    ! [A_15443] : k3_xboole_0('#skF_10',k4_xboole_0(A_15443,'#skF_12')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_91498,c_5784])).

tff(c_450,plain,(
    ! [A_98,B_99] :
      ( r2_hidden('#skF_2'(A_98,B_99),A_98)
      | r1_tarski(A_98,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_36,plain,(
    ! [D_23,A_18,B_19] :
      ( r2_hidden(D_23,A_18)
      | ~ r2_hidden(D_23,k4_xboole_0(A_18,B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_19037,plain,(
    ! [A_6874,B_6875,B_6876] :
      ( r2_hidden('#skF_2'(k4_xboole_0(A_6874,B_6875),B_6876),A_6874)
      | r1_tarski(k4_xboole_0(A_6874,B_6875),B_6876) ) ),
    inference(resolution,[status(thm)],[c_450,c_36])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( ~ r2_hidden('#skF_2'(A_7,B_8),B_8)
      | r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_19119,plain,(
    ! [A_6905,B_6906] : r1_tarski(k4_xboole_0(A_6905,B_6906),A_6905) ),
    inference(resolution,[status(thm)],[c_19037,c_10])).

tff(c_66,plain,(
    ! [A_31,B_32] :
      ( k3_xboole_0(A_31,B_32) = A_31
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_19223,plain,(
    ! [A_6965,B_6966] : k3_xboole_0(k4_xboole_0(A_6965,B_6966),A_6965) = k4_xboole_0(A_6965,B_6966) ),
    inference(resolution,[status(thm)],[c_19119,c_66])).

tff(c_19511,plain,(
    ! [A_6965,B_6966] : k3_xboole_0(A_6965,k4_xboole_0(A_6965,B_6966)) = k4_xboole_0(A_6965,B_6966) ),
    inference(superposition,[status(thm),theory(equality)],[c_19223,c_2])).

tff(c_92058,plain,(
    k4_xboole_0('#skF_10','#skF_12') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_91664,c_19511])).

tff(c_950,plain,(
    ! [D_1624,A_1625,B_1626] :
      ( r2_hidden(D_1624,k4_xboole_0(A_1625,B_1626))
      | r2_hidden(D_1624,B_1626)
      | ~ r2_hidden(D_1624,A_1625) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_979,plain,(
    ! [A_1625,B_1626,D_1624] :
      ( ~ v1_xboole_0(k4_xboole_0(A_1625,B_1626))
      | r2_hidden(D_1624,B_1626)
      | ~ r2_hidden(D_1624,A_1625) ) ),
    inference(resolution,[status(thm)],[c_950,c_4])).

tff(c_92765,plain,(
    ! [D_1624] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | r2_hidden(D_1624,'#skF_12')
      | ~ r2_hidden(D_1624,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92058,c_979])).

tff(c_93868,plain,(
    ! [D_15561] :
      ( r2_hidden(D_15561,'#skF_12')
      | ~ r2_hidden(D_15561,'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_92765])).

tff(c_119479,plain,(
    ! [B_34890] :
      ( r2_hidden('#skF_2'('#skF_10',B_34890),'#skF_12')
      | r1_tarski('#skF_10',B_34890) ) ),
    inference(resolution,[status(thm)],[c_12,c_93868])).

tff(c_119509,plain,(
    r1_tarski('#skF_10','#skF_12') ),
    inference(resolution,[status(thm)],[c_119479,c_10])).

tff(c_50,plain,(
    ! [A_24,B_25] :
      ( r2_xboole_0(A_24,B_25)
      | B_25 = A_24
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_58,plain,(
    ! [A_26,B_27] :
      ( r2_hidden('#skF_7'(A_26,B_27),B_27)
      | ~ r2_xboole_0(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2051,plain,(
    ! [A_2255,C_2256] : k3_xboole_0(k2_zfmisc_1(A_2255,C_2256),k2_zfmisc_1('#skF_12','#skF_13')) = k2_zfmisc_1(k3_xboole_0(A_2255,'#skF_10'),k3_xboole_0(C_2256,'#skF_11')) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_1990])).

tff(c_2617,plain,(
    ! [A_2535,C_2536] : k2_zfmisc_1(k3_xboole_0(A_2535,'#skF_10'),k3_xboole_0(C_2536,'#skF_11')) = k2_zfmisc_1(k3_xboole_0(A_2535,'#skF_12'),k3_xboole_0(C_2536,'#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_2051])).

tff(c_8370,plain,(
    ! [B_4694,C_4695] : k2_zfmisc_1(k3_xboole_0(B_4694,'#skF_12'),k3_xboole_0(C_4695,'#skF_13')) = k2_zfmisc_1(k3_xboole_0('#skF_10',B_4694),k3_xboole_0(C_4695,'#skF_11')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2617])).

tff(c_8538,plain,(
    ! [B_4694] : k2_zfmisc_1(k3_xboole_0('#skF_10',B_4694),k3_xboole_0('#skF_13','#skF_11')) = k2_zfmisc_1(k3_xboole_0(B_4694,'#skF_12'),'#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_8370])).

tff(c_88908,plain,(
    ! [A_15325] : k2_zfmisc_1(k3_xboole_0(k4_xboole_0(A_15325,'#skF_10'),'#skF_12'),'#skF_13') = k2_zfmisc_1(k1_xboole_0,k3_xboole_0('#skF_13','#skF_11')) ),
    inference(superposition,[status(thm),theory(equality)],[c_88664,c_8538])).

tff(c_108360,plain,(
    ! [A_31964] : k2_zfmisc_1(k3_xboole_0('#skF_12',k4_xboole_0(A_31964,'#skF_10')),'#skF_13') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_88,c_88908])).

tff(c_108455,plain,(
    k2_zfmisc_1(k4_xboole_0('#skF_12','#skF_10'),'#skF_13') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_19511,c_108360])).

tff(c_108543,plain,
    ( k1_xboole_0 = '#skF_13'
    | k4_xboole_0('#skF_12','#skF_10') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_108455,c_84])).

tff(c_108546,plain,(
    k4_xboole_0('#skF_12','#skF_10') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_108543])).

tff(c_108778,plain,(
    ! [D_1624] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | r2_hidden(D_1624,'#skF_10')
      | ~ r2_hidden(D_1624,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108546,c_979])).

tff(c_108871,plain,(
    ! [D_32189] :
      ( r2_hidden(D_32189,'#skF_10')
      | ~ r2_hidden(D_32189,'#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_108778])).

tff(c_56,plain,(
    ! [A_26,B_27] :
      ( ~ r2_hidden('#skF_7'(A_26,B_27),A_26)
      | ~ r2_xboole_0(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_122281,plain,(
    ! [B_35635] :
      ( ~ r2_xboole_0('#skF_10',B_35635)
      | ~ r2_hidden('#skF_7'('#skF_10',B_35635),'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_108871,c_56])).

tff(c_122321,plain,(
    ~ r2_xboole_0('#skF_10','#skF_12') ),
    inference(resolution,[status(thm)],[c_58,c_122281])).

tff(c_122324,plain,
    ( '#skF_10' = '#skF_12'
    | ~ r1_tarski('#skF_10','#skF_12') ),
    inference(resolution,[status(thm)],[c_50,c_122321])).

tff(c_122327,plain,(
    '#skF_10' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_119509,c_122324])).

tff(c_122329,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_122327])).

tff(c_122330,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_108543])).

tff(c_19911,plain,(
    ! [A_7024,B_7025] : k3_xboole_0(A_7024,k4_xboole_0(A_7024,B_7025)) = k4_xboole_0(A_7024,B_7025) ),
    inference(superposition,[status(thm),theory(equality)],[c_19223,c_2])).

tff(c_86,plain,(
    ! [A_40] : k2_zfmisc_1(A_40,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_371,plain,(
    ! [D_82,A_83,B_84] :
      ( r2_hidden(D_82,A_83)
      | ~ r2_hidden(D_82,k4_xboole_0(A_83,B_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2725,plain,(
    ! [A_2595,B_2596] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_2595,B_2596)),A_2595)
      | v1_xboole_0(k4_xboole_0(A_2595,B_2596)) ) ),
    inference(resolution,[status(thm)],[c_6,c_371])).

tff(c_2771,plain,(
    ! [A_2625,B_2626] :
      ( ~ v1_xboole_0(A_2625)
      | v1_xboole_0(k4_xboole_0(A_2625,B_2626)) ) ),
    inference(resolution,[status(thm)],[c_2725,c_4])).

tff(c_344,plain,(
    ! [D_79,B_80,A_81] :
      ( r2_hidden(D_79,B_80)
      | ~ r2_hidden(D_79,k3_xboole_0(A_81,B_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1611,plain,(
    ! [A_1987,B_1988] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_1987,B_1988)),B_1988)
      | v1_xboole_0(k3_xboole_0(A_1987,B_1988)) ) ),
    inference(resolution,[status(thm)],[c_6,c_344])).

tff(c_1671,plain,(
    ! [B_2017,A_2018] :
      ( ~ v1_xboole_0(B_2017)
      | v1_xboole_0(k3_xboole_0(A_2018,B_2017)) ) ),
    inference(resolution,[status(thm)],[c_1611,c_4])).

tff(c_486,plain,(
    ! [B_100] : r1_tarski(k1_xboole_0,B_100) ),
    inference(resolution,[status(thm)],[c_450,c_315])).

tff(c_407,plain,(
    ! [A_89,B_90] :
      ( r2_xboole_0(A_89,B_90)
      | B_90 = A_89
      | ~ r1_tarski(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_322,plain,(
    ! [A_74,B_75] :
      ( r2_hidden('#skF_7'(A_74,B_75),B_75)
      | ~ r2_xboole_0(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_341,plain,(
    ! [B_75,A_74] :
      ( ~ v1_xboole_0(B_75)
      | ~ r2_xboole_0(A_74,B_75) ) ),
    inference(resolution,[status(thm)],[c_322,c_4])).

tff(c_422,plain,(
    ! [B_90,A_89] :
      ( ~ v1_xboole_0(B_90)
      | B_90 = A_89
      | ~ r1_tarski(A_89,B_90) ) ),
    inference(resolution,[status(thm)],[c_407,c_341])).

tff(c_499,plain,(
    ! [B_100] :
      ( ~ v1_xboole_0(B_100)
      | k1_xboole_0 = B_100 ) ),
    inference(resolution,[status(thm)],[c_486,c_422])).

tff(c_1700,plain,(
    ! [A_2018,B_2017] :
      ( k3_xboole_0(A_2018,B_2017) = k1_xboole_0
      | ~ v1_xboole_0(B_2017) ) ),
    inference(resolution,[status(thm)],[c_1671,c_499])).

tff(c_2798,plain,(
    ! [A_2018,A_2625,B_2626] :
      ( k3_xboole_0(A_2018,k4_xboole_0(A_2625,B_2626)) = k1_xboole_0
      | ~ v1_xboole_0(A_2625) ) ),
    inference(resolution,[status(thm)],[c_2771,c_1700])).

tff(c_3510,plain,(
    ! [D_2963] : k2_zfmisc_1(k3_xboole_0('#skF_12','#skF_10'),k3_xboole_0('#skF_13',D_2963)) = k2_zfmisc_1('#skF_10',k3_xboole_0('#skF_11',D_2963)) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_3176])).

tff(c_3533,plain,(
    ! [A_2625,B_2626] :
      ( k2_zfmisc_1('#skF_10',k3_xboole_0('#skF_11',k4_xboole_0(A_2625,B_2626))) = k2_zfmisc_1(k3_xboole_0('#skF_12','#skF_10'),k1_xboole_0)
      | ~ v1_xboole_0(A_2625) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2798,c_3510])).

tff(c_3570,plain,(
    ! [A_2625,B_2626] :
      ( k2_zfmisc_1('#skF_10',k3_xboole_0('#skF_11',k4_xboole_0(A_2625,B_2626))) = k1_xboole_0
      | ~ v1_xboole_0(A_2625) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_3533])).

tff(c_20032,plain,(
    ! [B_7025] :
      ( k2_zfmisc_1('#skF_10',k4_xboole_0('#skF_11',B_7025)) = k1_xboole_0
      | ~ v1_xboole_0('#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19911,c_3570])).

tff(c_21942,plain,(
    ~ v1_xboole_0('#skF_11') ),
    inference(splitLeft,[status(thm)],[c_20032])).

tff(c_3230,plain,(
    ! [D_2841] : k2_zfmisc_1(k3_xboole_0('#skF_12','#skF_10'),k3_xboole_0('#skF_13',D_2841)) = k2_zfmisc_1('#skF_10',k3_xboole_0('#skF_11',D_2841)) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_3176])).

tff(c_89460,plain,(
    ! [A_15325] : k2_zfmisc_1('#skF_10',k3_xboole_0('#skF_11',k4_xboole_0(A_15325,'#skF_13'))) = k2_zfmisc_1(k3_xboole_0('#skF_12','#skF_10'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_88664,c_3230])).

tff(c_96624,plain,(
    ! [A_16210] : k2_zfmisc_1('#skF_10',k3_xboole_0('#skF_11',k4_xboole_0(A_16210,'#skF_13'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_89460])).

tff(c_96,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2066,plain,(
    ! [A_2255,C_2256] : k2_zfmisc_1(k3_xboole_0(A_2255,'#skF_10'),k3_xboole_0(C_2256,'#skF_11')) = k2_zfmisc_1(k3_xboole_0(A_2255,'#skF_12'),k3_xboole_0(C_2256,'#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_2051])).

tff(c_8713,plain,(
    ! [B_4785,A_4786] : k2_zfmisc_1(k3_xboole_0('#skF_10',B_4785),k3_xboole_0(A_4786,'#skF_11')) = k2_zfmisc_1(k3_xboole_0('#skF_12',B_4785),k3_xboole_0('#skF_13',A_4786)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3176])).

tff(c_8810,plain,(
    ! [C_2256] : k2_zfmisc_1(k3_xboole_0('#skF_10','#skF_12'),k3_xboole_0(C_2256,'#skF_13')) = k2_zfmisc_1(k3_xboole_0('#skF_12','#skF_10'),k3_xboole_0('#skF_13',C_2256)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2066,c_8713])).

tff(c_40869,plain,(
    ! [C_11025] : k2_zfmisc_1(k3_xboole_0('#skF_12','#skF_10'),k3_xboole_0(C_11025,'#skF_13')) = k2_zfmisc_1('#skF_10',k3_xboole_0('#skF_11',C_11025)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3230,c_2,c_8810])).

tff(c_2655,plain,(
    ! [C_2536] : k2_zfmisc_1(k3_xboole_0('#skF_10','#skF_12'),k3_xboole_0(C_2536,'#skF_13')) = k2_zfmisc_1('#skF_10',k3_xboole_0(C_2536,'#skF_11')) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_2617])).

tff(c_2692,plain,(
    ! [C_2536] : k2_zfmisc_1(k3_xboole_0('#skF_12','#skF_10'),k3_xboole_0(C_2536,'#skF_13')) = k2_zfmisc_1('#skF_10',k3_xboole_0(C_2536,'#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2655])).

tff(c_41027,plain,(
    ! [C_11054] : k2_zfmisc_1('#skF_10',k3_xboole_0(C_11054,'#skF_11')) = k2_zfmisc_1('#skF_10',k3_xboole_0('#skF_11',C_11054)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40869,c_2692])).

tff(c_41069,plain,(
    ! [C_11054] :
      ( k3_xboole_0(C_11054,'#skF_11') = k1_xboole_0
      | k1_xboole_0 = '#skF_10'
      | k2_zfmisc_1('#skF_10',k3_xboole_0('#skF_11',C_11054)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41027,c_84])).

tff(c_41155,plain,(
    ! [C_11054] :
      ( k3_xboole_0(C_11054,'#skF_11') = k1_xboole_0
      | k2_zfmisc_1('#skF_10',k3_xboole_0('#skF_11',C_11054)) != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_41069])).

tff(c_96788,plain,(
    ! [A_16239] : k3_xboole_0(k4_xboole_0(A_16239,'#skF_13'),'#skF_11') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_96624,c_41155])).

tff(c_19194,plain,(
    ! [A_6905,B_6906] : k3_xboole_0(k4_xboole_0(A_6905,B_6906),A_6905) = k4_xboole_0(A_6905,B_6906) ),
    inference(resolution,[status(thm)],[c_19119,c_66])).

tff(c_97179,plain,(
    k4_xboole_0('#skF_11','#skF_13') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_96788,c_19194])).

tff(c_32,plain,(
    ! [D_23,A_18,B_19] :
      ( r2_hidden(D_23,k4_xboole_0(A_18,B_19))
      | r2_hidden(D_23,B_19)
      | ~ r2_hidden(D_23,A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_98745,plain,(
    ! [D_23] :
      ( r2_hidden(D_23,k1_xboole_0)
      | r2_hidden(D_23,'#skF_13')
      | ~ r2_hidden(D_23,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97179,c_32])).

tff(c_104990,plain,(
    ! [D_30587] :
      ( r2_hidden(D_30587,'#skF_13')
      | ~ r2_hidden(D_30587,'#skF_11') ) ),
    inference(negUnitSimplification,[status(thm)],[c_315,c_98745])).

tff(c_105347,plain,
    ( r2_hidden('#skF_1'('#skF_11'),'#skF_13')
    | v1_xboole_0('#skF_11') ),
    inference(resolution,[status(thm)],[c_6,c_104990])).

tff(c_105434,plain,(
    r2_hidden('#skF_1'('#skF_11'),'#skF_13') ),
    inference(negUnitSimplification,[status(thm)],[c_21942,c_105347])).

tff(c_8,plain,(
    ! [C_11,B_8,A_7] :
      ( r2_hidden(C_11,B_8)
      | ~ r2_hidden(C_11,A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_105991,plain,(
    ! [B_31044] :
      ( r2_hidden('#skF_1'('#skF_11'),B_31044)
      | ~ r1_tarski('#skF_13',B_31044) ) ),
    inference(resolution,[status(thm)],[c_105434,c_8])).

tff(c_106100,plain,(
    ~ r1_tarski('#skF_13',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_105991,c_315])).

tff(c_122334,plain,(
    ~ r1_tarski('#skF_13','#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122330,c_106100])).

tff(c_122507,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_122334])).

tff(c_122509,plain,(
    v1_xboole_0('#skF_11') ),
    inference(splitRight,[status(thm)],[c_20032])).

tff(c_123047,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_122509,c_499])).

tff(c_123069,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_123047])).

tff(c_123070,plain,(
    '#skF_11' != '#skF_13' ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_123392,plain,(
    ! [D_35850,B_35851,A_35852] :
      ( ~ r2_hidden(D_35850,B_35851)
      | ~ r2_hidden(D_35850,k4_xboole_0(A_35852,B_35851)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_123411,plain,(
    ! [D_35853,A_35854] :
      ( ~ r2_hidden(D_35853,A_35854)
      | ~ r2_hidden(D_35853,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_123392])).

tff(c_123423,plain,(
    ! [C_39] : ~ r2_hidden(C_39,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_74,c_123411])).

tff(c_126037,plain,(
    ! [A_38457,B_38458,C_38459] :
      ( r2_hidden('#skF_3'(A_38457,B_38458,C_38459),B_38458)
      | r2_hidden('#skF_4'(A_38457,B_38458,C_38459),C_38459)
      | k3_xboole_0(A_38457,B_38458) = C_38459 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_126105,plain,(
    ! [A_38457,B_38458] :
      ( r2_hidden('#skF_3'(A_38457,B_38458,k1_xboole_0),B_38458)
      | k3_xboole_0(A_38457,B_38458) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_126037,c_123423])).

tff(c_125692,plain,(
    ! [A_38247,B_38248,C_38249] :
      ( r2_hidden('#skF_3'(A_38247,B_38248,C_38249),A_38247)
      | r2_hidden('#skF_4'(A_38247,B_38248,C_38249),C_38249)
      | k3_xboole_0(A_38247,B_38248) = C_38249 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_178249,plain,(
    ! [A_48700,B_48701,B_48702,C_48703] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_48700,B_48701),B_48702,C_48703),B_48701)
      | r2_hidden('#skF_4'(k4_xboole_0(A_48700,B_48701),B_48702,C_48703),C_48703)
      | k3_xboole_0(k4_xboole_0(A_48700,B_48701),B_48702) = C_48703 ) ),
    inference(resolution,[status(thm)],[c_125692,c_34])).

tff(c_178294,plain,(
    ! [A_48700,B_38458] :
      ( r2_hidden('#skF_4'(k4_xboole_0(A_48700,B_38458),B_38458,k1_xboole_0),k1_xboole_0)
      | k3_xboole_0(k4_xboole_0(A_48700,B_38458),B_38458) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_126105,c_178249])).

tff(c_178331,plain,(
    ! [A_48700,B_38458] :
      ( r2_hidden('#skF_4'(k4_xboole_0(A_48700,B_38458),B_38458,k1_xboole_0),k1_xboole_0)
      | k3_xboole_0(B_38458,k4_xboole_0(A_48700,B_38458)) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_178294])).

tff(c_178339,plain,(
    ! [B_48732,A_48733] : k3_xboole_0(B_48732,k4_xboole_0(A_48733,B_48732)) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_123423,c_178331])).

tff(c_123071,plain,(
    '#skF_10' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_123072,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_123071,c_96])).

tff(c_123241,plain,(
    ! [A_35825,B_35826] :
      ( k3_xboole_0(A_35825,B_35826) = A_35825
      | ~ r1_tarski(A_35825,B_35826) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_123245,plain,(
    ! [B_30] : k3_xboole_0(B_30,B_30) = B_30 ),
    inference(resolution,[status(thm)],[c_64,c_123241])).

tff(c_123077,plain,(
    k2_zfmisc_1('#skF_12','#skF_11') = k2_zfmisc_1('#skF_12','#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123071,c_98])).

tff(c_125600,plain,(
    ! [A_38215,C_38216,B_38217,D_38218] : k3_xboole_0(k2_zfmisc_1(A_38215,C_38216),k2_zfmisc_1(B_38217,D_38218)) = k2_zfmisc_1(k3_xboole_0(A_38215,B_38217),k3_xboole_0(C_38216,D_38218)) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_125679,plain,(
    ! [A_38215,C_38216] : k3_xboole_0(k2_zfmisc_1(A_38215,C_38216),k2_zfmisc_1('#skF_12','#skF_13')) = k2_zfmisc_1(k3_xboole_0(A_38215,'#skF_12'),k3_xboole_0(C_38216,'#skF_11')) ),
    inference(superposition,[status(thm),theory(equality)],[c_123077,c_125600])).

tff(c_125766,plain,(
    ! [A_38278,C_38279] : k2_zfmisc_1(k3_xboole_0(A_38278,'#skF_12'),k3_xboole_0(C_38279,'#skF_11')) = k2_zfmisc_1(k3_xboole_0(A_38278,'#skF_12'),k3_xboole_0(C_38279,'#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_125679])).

tff(c_125804,plain,(
    ! [C_38279] : k2_zfmisc_1(k3_xboole_0('#skF_12','#skF_12'),k3_xboole_0(C_38279,'#skF_13')) = k2_zfmisc_1('#skF_12',k3_xboole_0(C_38279,'#skF_11')) ),
    inference(superposition,[status(thm),theory(equality)],[c_123245,c_125766])).

tff(c_127646,plain,(
    ! [C_39127] : k2_zfmisc_1('#skF_12',k3_xboole_0(C_39127,'#skF_11')) = k2_zfmisc_1('#skF_12',k3_xboole_0(C_39127,'#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123245,c_125804])).

tff(c_127661,plain,(
    ! [C_39127] :
      ( k3_xboole_0(C_39127,'#skF_11') = k1_xboole_0
      | k1_xboole_0 = '#skF_12'
      | k2_zfmisc_1('#skF_12',k3_xboole_0(C_39127,'#skF_13')) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127646,c_84])).

tff(c_129557,plain,(
    ! [C_39870] :
      ( k3_xboole_0(C_39870,'#skF_11') = k1_xboole_0
      | k2_zfmisc_1('#skF_12',k3_xboole_0(C_39870,'#skF_13')) != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_123072,c_127661])).

tff(c_129609,plain,(
    ! [B_2] :
      ( k3_xboole_0(B_2,'#skF_11') = k1_xboole_0
      | k2_zfmisc_1('#skF_12',k3_xboole_0('#skF_13',B_2)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_129557])).

tff(c_178786,plain,(
    ! [A_48733] :
      ( k3_xboole_0(k4_xboole_0(A_48733,'#skF_13'),'#skF_11') = k1_xboole_0
      | k2_zfmisc_1('#skF_12',k1_xboole_0) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_178339,c_129609])).

tff(c_180038,plain,(
    ! [A_48792] : k3_xboole_0('#skF_11',k4_xboole_0(A_48792,'#skF_13')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_2,c_178786])).

tff(c_123351,plain,(
    ! [A_35842,B_35843] :
      ( r2_hidden('#skF_2'(A_35842,B_35843),A_35842)
      | r1_tarski(A_35842,B_35843) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_134468,plain,(
    ! [A_41425,B_41426,B_41427] :
      ( r2_hidden('#skF_2'(k4_xboole_0(A_41425,B_41426),B_41427),A_41425)
      | r1_tarski(k4_xboole_0(A_41425,B_41426),B_41427) ) ),
    inference(resolution,[status(thm)],[c_123351,c_36])).

tff(c_134544,plain,(
    ! [A_41456,B_41457] : r1_tarski(k4_xboole_0(A_41456,B_41457),A_41456) ),
    inference(resolution,[status(thm)],[c_134468,c_10])).

tff(c_135667,plain,(
    ! [A_41698,B_41699] : k3_xboole_0(k4_xboole_0(A_41698,B_41699),A_41698) = k4_xboole_0(A_41698,B_41699) ),
    inference(resolution,[status(thm)],[c_134544,c_66])).

tff(c_135982,plain,(
    ! [A_1,B_41699] : k3_xboole_0(A_1,k4_xboole_0(A_1,B_41699)) = k4_xboole_0(A_1,B_41699) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_135667])).

tff(c_180290,plain,(
    k4_xboole_0('#skF_11','#skF_13') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_180038,c_135982])).

tff(c_180768,plain,(
    ! [D_23] :
      ( r2_hidden(D_23,k1_xboole_0)
      | r2_hidden(D_23,'#skF_13')
      | ~ r2_hidden(D_23,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180290,c_32])).

tff(c_181952,plain,(
    ! [D_48910] :
      ( r2_hidden(D_48910,'#skF_13')
      | ~ r2_hidden(D_48910,'#skF_11') ) ),
    inference(negUnitSimplification,[status(thm)],[c_123423,c_180768])).

tff(c_193620,plain,(
    ! [B_62214] :
      ( r2_hidden('#skF_2'('#skF_11',B_62214),'#skF_13')
      | r1_tarski('#skF_11',B_62214) ) ),
    inference(resolution,[status(thm)],[c_12,c_181952])).

tff(c_193650,plain,(
    r1_tarski('#skF_11','#skF_13') ),
    inference(resolution,[status(thm)],[c_193620,c_10])).

tff(c_125676,plain,(
    ! [B_38217,D_38218] : k3_xboole_0(k2_zfmisc_1('#skF_12','#skF_13'),k2_zfmisc_1(B_38217,D_38218)) = k2_zfmisc_1(k3_xboole_0('#skF_12',B_38217),k3_xboole_0('#skF_11',D_38218)) ),
    inference(superposition,[status(thm),theory(equality)],[c_123077,c_125600])).

tff(c_126189,plain,(
    ! [B_38547,D_38548] : k2_zfmisc_1(k3_xboole_0('#skF_12',B_38547),k3_xboole_0('#skF_11',D_38548)) = k2_zfmisc_1(k3_xboole_0('#skF_12',B_38547),k3_xboole_0('#skF_13',D_38548)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_125676])).

tff(c_126235,plain,(
    ! [D_38548] : k2_zfmisc_1(k3_xboole_0('#skF_12','#skF_12'),k3_xboole_0('#skF_13',D_38548)) = k2_zfmisc_1('#skF_12',k3_xboole_0('#skF_11',D_38548)) ),
    inference(superposition,[status(thm),theory(equality)],[c_123245,c_126189])).

tff(c_126274,plain,(
    ! [D_38548] : k2_zfmisc_1('#skF_12',k3_xboole_0('#skF_11',D_38548)) = k2_zfmisc_1('#skF_12',k3_xboole_0('#skF_13',D_38548)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123245,c_126235])).

tff(c_178824,plain,(
    ! [A_48733] : k2_zfmisc_1('#skF_12',k3_xboole_0('#skF_13',k4_xboole_0(A_48733,'#skF_11'))) = k2_zfmisc_1('#skF_12',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_178339,c_126274])).

tff(c_184343,plain,(
    ! [A_49500] : k2_zfmisc_1('#skF_12',k3_xboole_0('#skF_13',k4_xboole_0(A_49500,'#skF_11'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_178824])).

tff(c_127214,plain,(
    ! [B_39005,B_39006] : k2_zfmisc_1(k3_xboole_0('#skF_12',B_39005),k3_xboole_0(B_39006,'#skF_11')) = k2_zfmisc_1(k3_xboole_0('#skF_12',B_39005),k3_xboole_0('#skF_13',B_39006)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_126189])).

tff(c_125690,plain,(
    ! [A_38215,C_38216] : k2_zfmisc_1(k3_xboole_0(A_38215,'#skF_12'),k3_xboole_0(C_38216,'#skF_11')) = k2_zfmisc_1(k3_xboole_0(A_38215,'#skF_12'),k3_xboole_0(C_38216,'#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_125679])).

tff(c_127232,plain,(
    ! [B_39006] : k2_zfmisc_1(k3_xboole_0('#skF_12','#skF_12'),k3_xboole_0(B_39006,'#skF_13')) = k2_zfmisc_1(k3_xboole_0('#skF_12','#skF_12'),k3_xboole_0('#skF_13',B_39006)) ),
    inference(superposition,[status(thm),theory(equality)],[c_127214,c_125690])).

tff(c_128984,plain,(
    ! [B_39691] : k2_zfmisc_1('#skF_12',k3_xboole_0(B_39691,'#skF_13')) = k2_zfmisc_1('#skF_12',k3_xboole_0('#skF_13',B_39691)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123245,c_123245,c_127232])).

tff(c_129019,plain,(
    ! [B_39691] :
      ( k3_xboole_0('#skF_13',B_39691) = k1_xboole_0
      | k1_xboole_0 = '#skF_12'
      | k2_zfmisc_1('#skF_12',k3_xboole_0(B_39691,'#skF_13')) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128984,c_84])).

tff(c_129649,plain,(
    ! [B_39930] :
      ( k3_xboole_0('#skF_13',B_39930) = k1_xboole_0
      | k2_zfmisc_1('#skF_12',k3_xboole_0(B_39930,'#skF_13')) != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_123072,c_129019])).

tff(c_129701,plain,(
    ! [B_2] :
      ( k3_xboole_0('#skF_13',B_2) = k1_xboole_0
      | k2_zfmisc_1('#skF_12',k3_xboole_0('#skF_13',B_2)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_129649])).

tff(c_184450,plain,(
    ! [A_49529] : k3_xboole_0('#skF_13',k4_xboole_0(A_49529,'#skF_11')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_184343,c_129701])).

tff(c_184738,plain,(
    k4_xboole_0('#skF_13','#skF_11') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_184450,c_135982])).

tff(c_185235,plain,(
    ! [D_23] :
      ( r2_hidden(D_23,k1_xboole_0)
      | r2_hidden(D_23,'#skF_11')
      | ~ r2_hidden(D_23,'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_184738,c_32])).

tff(c_185959,plain,(
    ! [D_49615] :
      ( r2_hidden(D_49615,'#skF_11')
      | ~ r2_hidden(D_49615,'#skF_13') ) ),
    inference(negUnitSimplification,[status(thm)],[c_123423,c_185235])).

tff(c_197233,plain,(
    ! [B_63482] :
      ( ~ r2_xboole_0('#skF_11',B_63482)
      | ~ r2_hidden('#skF_7'('#skF_11',B_63482),'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_185959,c_56])).

tff(c_197273,plain,(
    ~ r2_xboole_0('#skF_11','#skF_13') ),
    inference(resolution,[status(thm)],[c_58,c_197233])).

tff(c_197276,plain,
    ( '#skF_11' = '#skF_13'
    | ~ r1_tarski('#skF_11','#skF_13') ),
    inference(resolution,[status(thm)],[c_50,c_197273])).

tff(c_197279,plain,(
    '#skF_11' = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_193650,c_197276])).

tff(c_197281,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_123070,c_197279])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:03:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 42.52/29.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 42.63/29.77  
% 42.63/29.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 42.63/29.77  %$ r2_xboole_0 > r2_hidden > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_13 > #skF_5 > #skF_8 > #skF_3 > #skF_2 > #skF_7 > #skF_9 > #skF_12
% 42.63/29.77  
% 42.63/29.77  %Foreground sorts:
% 42.63/29.77  
% 42.63/29.77  
% 42.63/29.77  %Background operators:
% 42.63/29.77  
% 42.63/29.77  
% 42.63/29.77  %Foreground operators:
% 42.63/29.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 42.63/29.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 42.63/29.77  tff('#skF_11', type, '#skF_11': $i).
% 42.63/29.77  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 42.63/29.77  tff(k1_tarski, type, k1_tarski: $i > $i).
% 42.63/29.77  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 42.63/29.77  tff('#skF_1', type, '#skF_1': $i > $i).
% 42.63/29.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 42.63/29.77  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 42.63/29.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 42.63/29.77  tff('#skF_10', type, '#skF_10': $i).
% 42.63/29.77  tff('#skF_13', type, '#skF_13': $i).
% 42.63/29.77  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 42.63/29.77  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 42.63/29.77  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 42.63/29.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 42.63/29.77  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 42.63/29.77  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 42.63/29.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 42.63/29.77  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 42.63/29.77  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 42.63/29.77  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 42.63/29.77  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 42.63/29.77  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 42.63/29.77  tff('#skF_12', type, '#skF_12': $i).
% 42.63/29.77  
% 42.86/29.81  tff(f_116, negated_conjecture, ~(![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 42.86/29.81  tff(f_82, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 42.86/29.81  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 42.86/29.81  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 42.86/29.81  tff(f_97, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 42.86/29.81  tff(f_90, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 42.86/29.81  tff(f_59, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 42.86/29.81  tff(f_103, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 42.86/29.81  tff(f_49, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 42.86/29.81  tff(f_86, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 42.86/29.81  tff(f_105, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 42.86/29.81  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 42.86/29.81  tff(f_66, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 42.86/29.81  tff(f_76, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 42.86/29.81  tff(c_94, plain, (k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_116])).
% 42.86/29.81  tff(c_64, plain, (![B_30]: (r1_tarski(B_30, B_30))), inference(cnfTransformation, [status(thm)], [f_82])).
% 42.86/29.81  tff(c_92, plain, ('#skF_11'!='#skF_13' | '#skF_10'!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_116])).
% 42.86/29.81  tff(c_102, plain, ('#skF_10'!='#skF_12'), inference(splitLeft, [status(thm)], [c_92])).
% 42.86/29.81  tff(c_12, plain, (![A_7, B_8]: (r2_hidden('#skF_2'(A_7, B_8), A_7) | r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 42.86/29.81  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 42.86/29.81  tff(c_74, plain, (![C_39]: (r2_hidden(C_39, k1_tarski(C_39)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 42.86/29.81  tff(c_70, plain, (![A_34]: (k4_xboole_0(k1_xboole_0, A_34)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_90])).
% 42.86/29.81  tff(c_300, plain, (![D_68, B_69, A_70]: (~r2_hidden(D_68, B_69) | ~r2_hidden(D_68, k4_xboole_0(A_70, B_69)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 42.86/29.81  tff(c_309, plain, (![D_71, A_72]: (~r2_hidden(D_71, A_72) | ~r2_hidden(D_71, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_70, c_300])).
% 42.86/29.81  tff(c_316, plain, (![C_73]: (~r2_hidden(C_73, k1_xboole_0))), inference(resolution, [status(thm)], [c_74, c_309])).
% 42.86/29.81  tff(c_321, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_316])).
% 42.86/29.81  tff(c_88, plain, (![B_41]: (k2_zfmisc_1(k1_xboole_0, B_41)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_103])).
% 42.86/29.81  tff(c_315, plain, (![C_39]: (~r2_hidden(C_39, k1_xboole_0))), inference(resolution, [status(thm)], [c_74, c_309])).
% 42.86/29.81  tff(c_3813, plain, (![A_3111, B_3112, C_3113]: (r2_hidden('#skF_3'(A_3111, B_3112, C_3113), A_3111) | r2_hidden('#skF_4'(A_3111, B_3112, C_3113), C_3113) | k3_xboole_0(A_3111, B_3112)=C_3113)), inference(cnfTransformation, [status(thm)], [f_49])).
% 42.86/29.81  tff(c_3883, plain, (![A_3111, B_3112]: (r2_hidden('#skF_3'(A_3111, B_3112, k1_xboole_0), A_3111) | k3_xboole_0(A_3111, B_3112)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3813, c_315])).
% 42.86/29.81  tff(c_4384, plain, (![A_3354, B_3355, C_3356]: (r2_hidden('#skF_3'(A_3354, B_3355, C_3356), B_3355) | r2_hidden('#skF_4'(A_3354, B_3355, C_3356), C_3356) | k3_xboole_0(A_3354, B_3355)=C_3356)), inference(cnfTransformation, [status(thm)], [f_49])).
% 42.86/29.81  tff(c_34, plain, (![D_23, B_19, A_18]: (~r2_hidden(D_23, B_19) | ~r2_hidden(D_23, k4_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 42.86/29.81  tff(c_88545, plain, (![A_15292, A_15293, B_15294, C_15295]: (~r2_hidden('#skF_3'(A_15292, k4_xboole_0(A_15293, B_15294), C_15295), B_15294) | r2_hidden('#skF_4'(A_15292, k4_xboole_0(A_15293, B_15294), C_15295), C_15295) | k3_xboole_0(A_15292, k4_xboole_0(A_15293, B_15294))=C_15295)), inference(resolution, [status(thm)], [c_4384, c_34])).
% 42.86/29.81  tff(c_88617, plain, (![A_3111, A_15293]: (r2_hidden('#skF_4'(A_3111, k4_xboole_0(A_15293, A_3111), k1_xboole_0), k1_xboole_0) | k3_xboole_0(A_3111, k4_xboole_0(A_15293, A_3111))=k1_xboole_0)), inference(resolution, [status(thm)], [c_3883, c_88545])).
% 42.86/29.81  tff(c_88664, plain, (![A_15324, A_15325]: (k3_xboole_0(A_15324, k4_xboole_0(A_15325, A_15324))=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_315, c_88617])).
% 42.86/29.81  tff(c_266, plain, (![A_65, B_66]: (k3_xboole_0(A_65, B_66)=A_65 | ~r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_86])).
% 42.86/29.81  tff(c_270, plain, (![B_30]: (k3_xboole_0(B_30, B_30)=B_30)), inference(resolution, [status(thm)], [c_64, c_266])).
% 42.86/29.81  tff(c_90, plain, (![A_42, C_44, B_43, D_45]: (k3_xboole_0(k2_zfmisc_1(A_42, C_44), k2_zfmisc_1(B_43, D_45))=k2_zfmisc_1(k3_xboole_0(A_42, B_43), k3_xboole_0(C_44, D_45)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 42.86/29.81  tff(c_98, plain, (k2_zfmisc_1('#skF_10', '#skF_11')=k2_zfmisc_1('#skF_12', '#skF_13')), inference(cnfTransformation, [status(thm)], [f_116])).
% 42.86/29.81  tff(c_1990, plain, (![A_2255, C_2256, B_2257, D_2258]: (k3_xboole_0(k2_zfmisc_1(A_2255, C_2256), k2_zfmisc_1(B_2257, D_2258))=k2_zfmisc_1(k3_xboole_0(A_2255, B_2257), k3_xboole_0(C_2256, D_2258)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 42.86/29.81  tff(c_2048, plain, (![B_2257, D_2258]: (k3_xboole_0(k2_zfmisc_1('#skF_12', '#skF_13'), k2_zfmisc_1(B_2257, D_2258))=k2_zfmisc_1(k3_xboole_0('#skF_10', B_2257), k3_xboole_0('#skF_11', D_2258)))), inference(superposition, [status(thm), theory('equality')], [c_98, c_1990])).
% 42.86/29.81  tff(c_3176, plain, (![B_2840, D_2841]: (k2_zfmisc_1(k3_xboole_0('#skF_10', B_2840), k3_xboole_0('#skF_11', D_2841))=k2_zfmisc_1(k3_xboole_0('#skF_12', B_2840), k3_xboole_0('#skF_13', D_2841)))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_2048])).
% 42.86/29.81  tff(c_3234, plain, (![B_2840]: (k2_zfmisc_1(k3_xboole_0('#skF_12', B_2840), k3_xboole_0('#skF_13', '#skF_11'))=k2_zfmisc_1(k3_xboole_0('#skF_10', B_2840), '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_270, c_3176])).
% 42.86/29.81  tff(c_89453, plain, (![A_15325]: (k2_zfmisc_1(k3_xboole_0('#skF_10', k4_xboole_0(A_15325, '#skF_12')), '#skF_11')=k2_zfmisc_1(k1_xboole_0, k3_xboole_0('#skF_13', '#skF_11')))), inference(superposition, [status(thm), theory('equality')], [c_88664, c_3234])).
% 42.86/29.81  tff(c_91498, plain, (![A_15414]: (k2_zfmisc_1(k3_xboole_0('#skF_10', k4_xboole_0(A_15414, '#skF_12')), '#skF_11')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_88, c_89453])).
% 42.86/29.81  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 42.86/29.81  tff(c_4645, plain, (![A_3475, D_3476]: (k2_zfmisc_1(k3_xboole_0(A_3475, '#skF_10'), k3_xboole_0('#skF_11', D_3476))=k2_zfmisc_1(k3_xboole_0('#skF_12', A_3475), k3_xboole_0('#skF_13', D_3476)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3176])).
% 42.86/29.81  tff(c_4690, plain, (![B_2840]: (k2_zfmisc_1(k3_xboole_0(B_2840, '#skF_10'), k3_xboole_0('#skF_11', '#skF_11'))=k2_zfmisc_1(k3_xboole_0('#skF_10', B_2840), '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_3234, c_4645])).
% 42.86/29.81  tff(c_5043, plain, (![B_3681]: (k2_zfmisc_1(k3_xboole_0(B_3681, '#skF_10'), '#skF_11')=k2_zfmisc_1(k3_xboole_0('#skF_10', B_3681), '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_270, c_4690])).
% 42.86/29.81  tff(c_84, plain, (![B_41, A_40]: (k1_xboole_0=B_41 | k1_xboole_0=A_40 | k2_zfmisc_1(A_40, B_41)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_103])).
% 42.86/29.81  tff(c_5064, plain, (![B_3681]: (k1_xboole_0='#skF_11' | k3_xboole_0('#skF_10', B_3681)=k1_xboole_0 | k2_zfmisc_1(k3_xboole_0(B_3681, '#skF_10'), '#skF_11')!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5043, c_84])).
% 42.86/29.81  tff(c_5740, plain, (![B_3892]: (k3_xboole_0('#skF_10', B_3892)=k1_xboole_0 | k2_zfmisc_1(k3_xboole_0(B_3892, '#skF_10'), '#skF_11')!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_94, c_5064])).
% 42.86/29.81  tff(c_5784, plain, (![B_2]: (k3_xboole_0('#skF_10', B_2)=k1_xboole_0 | k2_zfmisc_1(k3_xboole_0('#skF_10', B_2), '#skF_11')!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_5740])).
% 42.86/29.81  tff(c_91664, plain, (![A_15443]: (k3_xboole_0('#skF_10', k4_xboole_0(A_15443, '#skF_12'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_91498, c_5784])).
% 42.86/29.81  tff(c_450, plain, (![A_98, B_99]: (r2_hidden('#skF_2'(A_98, B_99), A_98) | r1_tarski(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_40])).
% 42.86/29.81  tff(c_36, plain, (![D_23, A_18, B_19]: (r2_hidden(D_23, A_18) | ~r2_hidden(D_23, k4_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 42.86/29.81  tff(c_19037, plain, (![A_6874, B_6875, B_6876]: (r2_hidden('#skF_2'(k4_xboole_0(A_6874, B_6875), B_6876), A_6874) | r1_tarski(k4_xboole_0(A_6874, B_6875), B_6876))), inference(resolution, [status(thm)], [c_450, c_36])).
% 42.86/29.81  tff(c_10, plain, (![A_7, B_8]: (~r2_hidden('#skF_2'(A_7, B_8), B_8) | r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 42.86/29.81  tff(c_19119, plain, (![A_6905, B_6906]: (r1_tarski(k4_xboole_0(A_6905, B_6906), A_6905))), inference(resolution, [status(thm)], [c_19037, c_10])).
% 42.86/29.81  tff(c_66, plain, (![A_31, B_32]: (k3_xboole_0(A_31, B_32)=A_31 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_86])).
% 42.86/29.81  tff(c_19223, plain, (![A_6965, B_6966]: (k3_xboole_0(k4_xboole_0(A_6965, B_6966), A_6965)=k4_xboole_0(A_6965, B_6966))), inference(resolution, [status(thm)], [c_19119, c_66])).
% 42.86/29.81  tff(c_19511, plain, (![A_6965, B_6966]: (k3_xboole_0(A_6965, k4_xboole_0(A_6965, B_6966))=k4_xboole_0(A_6965, B_6966))), inference(superposition, [status(thm), theory('equality')], [c_19223, c_2])).
% 42.86/29.81  tff(c_92058, plain, (k4_xboole_0('#skF_10', '#skF_12')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_91664, c_19511])).
% 42.86/29.81  tff(c_950, plain, (![D_1624, A_1625, B_1626]: (r2_hidden(D_1624, k4_xboole_0(A_1625, B_1626)) | r2_hidden(D_1624, B_1626) | ~r2_hidden(D_1624, A_1625))), inference(cnfTransformation, [status(thm)], [f_59])).
% 42.86/29.81  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 42.86/29.81  tff(c_979, plain, (![A_1625, B_1626, D_1624]: (~v1_xboole_0(k4_xboole_0(A_1625, B_1626)) | r2_hidden(D_1624, B_1626) | ~r2_hidden(D_1624, A_1625))), inference(resolution, [status(thm)], [c_950, c_4])).
% 42.86/29.81  tff(c_92765, plain, (![D_1624]: (~v1_xboole_0(k1_xboole_0) | r2_hidden(D_1624, '#skF_12') | ~r2_hidden(D_1624, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_92058, c_979])).
% 42.86/29.81  tff(c_93868, plain, (![D_15561]: (r2_hidden(D_15561, '#skF_12') | ~r2_hidden(D_15561, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_321, c_92765])).
% 42.86/29.81  tff(c_119479, plain, (![B_34890]: (r2_hidden('#skF_2'('#skF_10', B_34890), '#skF_12') | r1_tarski('#skF_10', B_34890))), inference(resolution, [status(thm)], [c_12, c_93868])).
% 42.86/29.81  tff(c_119509, plain, (r1_tarski('#skF_10', '#skF_12')), inference(resolution, [status(thm)], [c_119479, c_10])).
% 42.86/29.81  tff(c_50, plain, (![A_24, B_25]: (r2_xboole_0(A_24, B_25) | B_25=A_24 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_66])).
% 42.86/29.81  tff(c_58, plain, (![A_26, B_27]: (r2_hidden('#skF_7'(A_26, B_27), B_27) | ~r2_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_76])).
% 42.86/29.81  tff(c_2051, plain, (![A_2255, C_2256]: (k3_xboole_0(k2_zfmisc_1(A_2255, C_2256), k2_zfmisc_1('#skF_12', '#skF_13'))=k2_zfmisc_1(k3_xboole_0(A_2255, '#skF_10'), k3_xboole_0(C_2256, '#skF_11')))), inference(superposition, [status(thm), theory('equality')], [c_98, c_1990])).
% 42.86/29.81  tff(c_2617, plain, (![A_2535, C_2536]: (k2_zfmisc_1(k3_xboole_0(A_2535, '#skF_10'), k3_xboole_0(C_2536, '#skF_11'))=k2_zfmisc_1(k3_xboole_0(A_2535, '#skF_12'), k3_xboole_0(C_2536, '#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_2051])).
% 42.86/29.81  tff(c_8370, plain, (![B_4694, C_4695]: (k2_zfmisc_1(k3_xboole_0(B_4694, '#skF_12'), k3_xboole_0(C_4695, '#skF_13'))=k2_zfmisc_1(k3_xboole_0('#skF_10', B_4694), k3_xboole_0(C_4695, '#skF_11')))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2617])).
% 42.86/29.81  tff(c_8538, plain, (![B_4694]: (k2_zfmisc_1(k3_xboole_0('#skF_10', B_4694), k3_xboole_0('#skF_13', '#skF_11'))=k2_zfmisc_1(k3_xboole_0(B_4694, '#skF_12'), '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_270, c_8370])).
% 42.86/29.81  tff(c_88908, plain, (![A_15325]: (k2_zfmisc_1(k3_xboole_0(k4_xboole_0(A_15325, '#skF_10'), '#skF_12'), '#skF_13')=k2_zfmisc_1(k1_xboole_0, k3_xboole_0('#skF_13', '#skF_11')))), inference(superposition, [status(thm), theory('equality')], [c_88664, c_8538])).
% 42.86/29.81  tff(c_108360, plain, (![A_31964]: (k2_zfmisc_1(k3_xboole_0('#skF_12', k4_xboole_0(A_31964, '#skF_10')), '#skF_13')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_88, c_88908])).
% 42.86/29.81  tff(c_108455, plain, (k2_zfmisc_1(k4_xboole_0('#skF_12', '#skF_10'), '#skF_13')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_19511, c_108360])).
% 42.86/29.81  tff(c_108543, plain, (k1_xboole_0='#skF_13' | k4_xboole_0('#skF_12', '#skF_10')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_108455, c_84])).
% 42.86/29.81  tff(c_108546, plain, (k4_xboole_0('#skF_12', '#skF_10')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_108543])).
% 42.86/29.81  tff(c_108778, plain, (![D_1624]: (~v1_xboole_0(k1_xboole_0) | r2_hidden(D_1624, '#skF_10') | ~r2_hidden(D_1624, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_108546, c_979])).
% 42.86/29.81  tff(c_108871, plain, (![D_32189]: (r2_hidden(D_32189, '#skF_10') | ~r2_hidden(D_32189, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_321, c_108778])).
% 42.86/29.81  tff(c_56, plain, (![A_26, B_27]: (~r2_hidden('#skF_7'(A_26, B_27), A_26) | ~r2_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_76])).
% 42.86/29.81  tff(c_122281, plain, (![B_35635]: (~r2_xboole_0('#skF_10', B_35635) | ~r2_hidden('#skF_7'('#skF_10', B_35635), '#skF_12'))), inference(resolution, [status(thm)], [c_108871, c_56])).
% 42.86/29.81  tff(c_122321, plain, (~r2_xboole_0('#skF_10', '#skF_12')), inference(resolution, [status(thm)], [c_58, c_122281])).
% 42.86/29.81  tff(c_122324, plain, ('#skF_10'='#skF_12' | ~r1_tarski('#skF_10', '#skF_12')), inference(resolution, [status(thm)], [c_50, c_122321])).
% 42.86/29.81  tff(c_122327, plain, ('#skF_10'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_119509, c_122324])).
% 42.86/29.81  tff(c_122329, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_122327])).
% 42.86/29.81  tff(c_122330, plain, (k1_xboole_0='#skF_13'), inference(splitRight, [status(thm)], [c_108543])).
% 42.86/29.81  tff(c_19911, plain, (![A_7024, B_7025]: (k3_xboole_0(A_7024, k4_xboole_0(A_7024, B_7025))=k4_xboole_0(A_7024, B_7025))), inference(superposition, [status(thm), theory('equality')], [c_19223, c_2])).
% 42.86/29.81  tff(c_86, plain, (![A_40]: (k2_zfmisc_1(A_40, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_103])).
% 42.86/29.81  tff(c_371, plain, (![D_82, A_83, B_84]: (r2_hidden(D_82, A_83) | ~r2_hidden(D_82, k4_xboole_0(A_83, B_84)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 42.86/29.81  tff(c_2725, plain, (![A_2595, B_2596]: (r2_hidden('#skF_1'(k4_xboole_0(A_2595, B_2596)), A_2595) | v1_xboole_0(k4_xboole_0(A_2595, B_2596)))), inference(resolution, [status(thm)], [c_6, c_371])).
% 42.86/29.81  tff(c_2771, plain, (![A_2625, B_2626]: (~v1_xboole_0(A_2625) | v1_xboole_0(k4_xboole_0(A_2625, B_2626)))), inference(resolution, [status(thm)], [c_2725, c_4])).
% 42.86/29.81  tff(c_344, plain, (![D_79, B_80, A_81]: (r2_hidden(D_79, B_80) | ~r2_hidden(D_79, k3_xboole_0(A_81, B_80)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 42.86/29.81  tff(c_1611, plain, (![A_1987, B_1988]: (r2_hidden('#skF_1'(k3_xboole_0(A_1987, B_1988)), B_1988) | v1_xboole_0(k3_xboole_0(A_1987, B_1988)))), inference(resolution, [status(thm)], [c_6, c_344])).
% 42.86/29.81  tff(c_1671, plain, (![B_2017, A_2018]: (~v1_xboole_0(B_2017) | v1_xboole_0(k3_xboole_0(A_2018, B_2017)))), inference(resolution, [status(thm)], [c_1611, c_4])).
% 42.86/29.81  tff(c_486, plain, (![B_100]: (r1_tarski(k1_xboole_0, B_100))), inference(resolution, [status(thm)], [c_450, c_315])).
% 42.86/29.81  tff(c_407, plain, (![A_89, B_90]: (r2_xboole_0(A_89, B_90) | B_90=A_89 | ~r1_tarski(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_66])).
% 42.86/29.81  tff(c_322, plain, (![A_74, B_75]: (r2_hidden('#skF_7'(A_74, B_75), B_75) | ~r2_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_76])).
% 42.86/29.81  tff(c_341, plain, (![B_75, A_74]: (~v1_xboole_0(B_75) | ~r2_xboole_0(A_74, B_75))), inference(resolution, [status(thm)], [c_322, c_4])).
% 42.86/29.81  tff(c_422, plain, (![B_90, A_89]: (~v1_xboole_0(B_90) | B_90=A_89 | ~r1_tarski(A_89, B_90))), inference(resolution, [status(thm)], [c_407, c_341])).
% 42.86/29.81  tff(c_499, plain, (![B_100]: (~v1_xboole_0(B_100) | k1_xboole_0=B_100)), inference(resolution, [status(thm)], [c_486, c_422])).
% 42.86/29.81  tff(c_1700, plain, (![A_2018, B_2017]: (k3_xboole_0(A_2018, B_2017)=k1_xboole_0 | ~v1_xboole_0(B_2017))), inference(resolution, [status(thm)], [c_1671, c_499])).
% 42.86/29.81  tff(c_2798, plain, (![A_2018, A_2625, B_2626]: (k3_xboole_0(A_2018, k4_xboole_0(A_2625, B_2626))=k1_xboole_0 | ~v1_xboole_0(A_2625))), inference(resolution, [status(thm)], [c_2771, c_1700])).
% 42.86/29.81  tff(c_3510, plain, (![D_2963]: (k2_zfmisc_1(k3_xboole_0('#skF_12', '#skF_10'), k3_xboole_0('#skF_13', D_2963))=k2_zfmisc_1('#skF_10', k3_xboole_0('#skF_11', D_2963)))), inference(superposition, [status(thm), theory('equality')], [c_270, c_3176])).
% 42.86/29.81  tff(c_3533, plain, (![A_2625, B_2626]: (k2_zfmisc_1('#skF_10', k3_xboole_0('#skF_11', k4_xboole_0(A_2625, B_2626)))=k2_zfmisc_1(k3_xboole_0('#skF_12', '#skF_10'), k1_xboole_0) | ~v1_xboole_0(A_2625))), inference(superposition, [status(thm), theory('equality')], [c_2798, c_3510])).
% 42.86/29.81  tff(c_3570, plain, (![A_2625, B_2626]: (k2_zfmisc_1('#skF_10', k3_xboole_0('#skF_11', k4_xboole_0(A_2625, B_2626)))=k1_xboole_0 | ~v1_xboole_0(A_2625))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_3533])).
% 42.86/29.81  tff(c_20032, plain, (![B_7025]: (k2_zfmisc_1('#skF_10', k4_xboole_0('#skF_11', B_7025))=k1_xboole_0 | ~v1_xboole_0('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_19911, c_3570])).
% 42.86/29.81  tff(c_21942, plain, (~v1_xboole_0('#skF_11')), inference(splitLeft, [status(thm)], [c_20032])).
% 42.86/29.81  tff(c_3230, plain, (![D_2841]: (k2_zfmisc_1(k3_xboole_0('#skF_12', '#skF_10'), k3_xboole_0('#skF_13', D_2841))=k2_zfmisc_1('#skF_10', k3_xboole_0('#skF_11', D_2841)))), inference(superposition, [status(thm), theory('equality')], [c_270, c_3176])).
% 42.86/29.81  tff(c_89460, plain, (![A_15325]: (k2_zfmisc_1('#skF_10', k3_xboole_0('#skF_11', k4_xboole_0(A_15325, '#skF_13')))=k2_zfmisc_1(k3_xboole_0('#skF_12', '#skF_10'), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_88664, c_3230])).
% 42.86/29.81  tff(c_96624, plain, (![A_16210]: (k2_zfmisc_1('#skF_10', k3_xboole_0('#skF_11', k4_xboole_0(A_16210, '#skF_13')))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_86, c_89460])).
% 42.86/29.81  tff(c_96, plain, (k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_116])).
% 42.86/29.81  tff(c_2066, plain, (![A_2255, C_2256]: (k2_zfmisc_1(k3_xboole_0(A_2255, '#skF_10'), k3_xboole_0(C_2256, '#skF_11'))=k2_zfmisc_1(k3_xboole_0(A_2255, '#skF_12'), k3_xboole_0(C_2256, '#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_2051])).
% 42.86/29.81  tff(c_8713, plain, (![B_4785, A_4786]: (k2_zfmisc_1(k3_xboole_0('#skF_10', B_4785), k3_xboole_0(A_4786, '#skF_11'))=k2_zfmisc_1(k3_xboole_0('#skF_12', B_4785), k3_xboole_0('#skF_13', A_4786)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3176])).
% 42.86/29.81  tff(c_8810, plain, (![C_2256]: (k2_zfmisc_1(k3_xboole_0('#skF_10', '#skF_12'), k3_xboole_0(C_2256, '#skF_13'))=k2_zfmisc_1(k3_xboole_0('#skF_12', '#skF_10'), k3_xboole_0('#skF_13', C_2256)))), inference(superposition, [status(thm), theory('equality')], [c_2066, c_8713])).
% 42.86/29.81  tff(c_40869, plain, (![C_11025]: (k2_zfmisc_1(k3_xboole_0('#skF_12', '#skF_10'), k3_xboole_0(C_11025, '#skF_13'))=k2_zfmisc_1('#skF_10', k3_xboole_0('#skF_11', C_11025)))), inference(demodulation, [status(thm), theory('equality')], [c_3230, c_2, c_8810])).
% 42.86/29.81  tff(c_2655, plain, (![C_2536]: (k2_zfmisc_1(k3_xboole_0('#skF_10', '#skF_12'), k3_xboole_0(C_2536, '#skF_13'))=k2_zfmisc_1('#skF_10', k3_xboole_0(C_2536, '#skF_11')))), inference(superposition, [status(thm), theory('equality')], [c_270, c_2617])).
% 42.86/29.81  tff(c_2692, plain, (![C_2536]: (k2_zfmisc_1(k3_xboole_0('#skF_12', '#skF_10'), k3_xboole_0(C_2536, '#skF_13'))=k2_zfmisc_1('#skF_10', k3_xboole_0(C_2536, '#skF_11')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2655])).
% 42.86/29.81  tff(c_41027, plain, (![C_11054]: (k2_zfmisc_1('#skF_10', k3_xboole_0(C_11054, '#skF_11'))=k2_zfmisc_1('#skF_10', k3_xboole_0('#skF_11', C_11054)))), inference(superposition, [status(thm), theory('equality')], [c_40869, c_2692])).
% 42.86/29.81  tff(c_41069, plain, (![C_11054]: (k3_xboole_0(C_11054, '#skF_11')=k1_xboole_0 | k1_xboole_0='#skF_10' | k2_zfmisc_1('#skF_10', k3_xboole_0('#skF_11', C_11054))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_41027, c_84])).
% 42.86/29.81  tff(c_41155, plain, (![C_11054]: (k3_xboole_0(C_11054, '#skF_11')=k1_xboole_0 | k2_zfmisc_1('#skF_10', k3_xboole_0('#skF_11', C_11054))!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_96, c_41069])).
% 42.86/29.81  tff(c_96788, plain, (![A_16239]: (k3_xboole_0(k4_xboole_0(A_16239, '#skF_13'), '#skF_11')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_96624, c_41155])).
% 42.86/29.81  tff(c_19194, plain, (![A_6905, B_6906]: (k3_xboole_0(k4_xboole_0(A_6905, B_6906), A_6905)=k4_xboole_0(A_6905, B_6906))), inference(resolution, [status(thm)], [c_19119, c_66])).
% 42.86/29.81  tff(c_97179, plain, (k4_xboole_0('#skF_11', '#skF_13')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_96788, c_19194])).
% 42.86/29.81  tff(c_32, plain, (![D_23, A_18, B_19]: (r2_hidden(D_23, k4_xboole_0(A_18, B_19)) | r2_hidden(D_23, B_19) | ~r2_hidden(D_23, A_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 42.86/29.81  tff(c_98745, plain, (![D_23]: (r2_hidden(D_23, k1_xboole_0) | r2_hidden(D_23, '#skF_13') | ~r2_hidden(D_23, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_97179, c_32])).
% 42.86/29.81  tff(c_104990, plain, (![D_30587]: (r2_hidden(D_30587, '#skF_13') | ~r2_hidden(D_30587, '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_315, c_98745])).
% 42.86/29.81  tff(c_105347, plain, (r2_hidden('#skF_1'('#skF_11'), '#skF_13') | v1_xboole_0('#skF_11')), inference(resolution, [status(thm)], [c_6, c_104990])).
% 42.86/29.81  tff(c_105434, plain, (r2_hidden('#skF_1'('#skF_11'), '#skF_13')), inference(negUnitSimplification, [status(thm)], [c_21942, c_105347])).
% 42.86/29.81  tff(c_8, plain, (![C_11, B_8, A_7]: (r2_hidden(C_11, B_8) | ~r2_hidden(C_11, A_7) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 42.86/29.81  tff(c_105991, plain, (![B_31044]: (r2_hidden('#skF_1'('#skF_11'), B_31044) | ~r1_tarski('#skF_13', B_31044))), inference(resolution, [status(thm)], [c_105434, c_8])).
% 42.86/29.81  tff(c_106100, plain, (~r1_tarski('#skF_13', k1_xboole_0)), inference(resolution, [status(thm)], [c_105991, c_315])).
% 42.86/29.81  tff(c_122334, plain, (~r1_tarski('#skF_13', '#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_122330, c_106100])).
% 42.86/29.81  tff(c_122507, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_122334])).
% 42.86/29.81  tff(c_122509, plain, (v1_xboole_0('#skF_11')), inference(splitRight, [status(thm)], [c_20032])).
% 42.86/29.81  tff(c_123047, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_122509, c_499])).
% 42.86/29.81  tff(c_123069, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_123047])).
% 42.86/29.81  tff(c_123070, plain, ('#skF_11'!='#skF_13'), inference(splitRight, [status(thm)], [c_92])).
% 42.86/29.81  tff(c_123392, plain, (![D_35850, B_35851, A_35852]: (~r2_hidden(D_35850, B_35851) | ~r2_hidden(D_35850, k4_xboole_0(A_35852, B_35851)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 42.86/29.81  tff(c_123411, plain, (![D_35853, A_35854]: (~r2_hidden(D_35853, A_35854) | ~r2_hidden(D_35853, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_70, c_123392])).
% 42.86/29.81  tff(c_123423, plain, (![C_39]: (~r2_hidden(C_39, k1_xboole_0))), inference(resolution, [status(thm)], [c_74, c_123411])).
% 42.86/29.81  tff(c_126037, plain, (![A_38457, B_38458, C_38459]: (r2_hidden('#skF_3'(A_38457, B_38458, C_38459), B_38458) | r2_hidden('#skF_4'(A_38457, B_38458, C_38459), C_38459) | k3_xboole_0(A_38457, B_38458)=C_38459)), inference(cnfTransformation, [status(thm)], [f_49])).
% 42.86/29.81  tff(c_126105, plain, (![A_38457, B_38458]: (r2_hidden('#skF_3'(A_38457, B_38458, k1_xboole_0), B_38458) | k3_xboole_0(A_38457, B_38458)=k1_xboole_0)), inference(resolution, [status(thm)], [c_126037, c_123423])).
% 42.86/29.81  tff(c_125692, plain, (![A_38247, B_38248, C_38249]: (r2_hidden('#skF_3'(A_38247, B_38248, C_38249), A_38247) | r2_hidden('#skF_4'(A_38247, B_38248, C_38249), C_38249) | k3_xboole_0(A_38247, B_38248)=C_38249)), inference(cnfTransformation, [status(thm)], [f_49])).
% 42.86/29.81  tff(c_178249, plain, (![A_48700, B_48701, B_48702, C_48703]: (~r2_hidden('#skF_3'(k4_xboole_0(A_48700, B_48701), B_48702, C_48703), B_48701) | r2_hidden('#skF_4'(k4_xboole_0(A_48700, B_48701), B_48702, C_48703), C_48703) | k3_xboole_0(k4_xboole_0(A_48700, B_48701), B_48702)=C_48703)), inference(resolution, [status(thm)], [c_125692, c_34])).
% 42.86/29.81  tff(c_178294, plain, (![A_48700, B_38458]: (r2_hidden('#skF_4'(k4_xboole_0(A_48700, B_38458), B_38458, k1_xboole_0), k1_xboole_0) | k3_xboole_0(k4_xboole_0(A_48700, B_38458), B_38458)=k1_xboole_0)), inference(resolution, [status(thm)], [c_126105, c_178249])).
% 42.86/29.81  tff(c_178331, plain, (![A_48700, B_38458]: (r2_hidden('#skF_4'(k4_xboole_0(A_48700, B_38458), B_38458, k1_xboole_0), k1_xboole_0) | k3_xboole_0(B_38458, k4_xboole_0(A_48700, B_38458))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_178294])).
% 42.86/29.81  tff(c_178339, plain, (![B_48732, A_48733]: (k3_xboole_0(B_48732, k4_xboole_0(A_48733, B_48732))=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_123423, c_178331])).
% 42.86/29.81  tff(c_123071, plain, ('#skF_10'='#skF_12'), inference(splitRight, [status(thm)], [c_92])).
% 42.86/29.81  tff(c_123072, plain, (k1_xboole_0!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_123071, c_96])).
% 42.86/29.81  tff(c_123241, plain, (![A_35825, B_35826]: (k3_xboole_0(A_35825, B_35826)=A_35825 | ~r1_tarski(A_35825, B_35826))), inference(cnfTransformation, [status(thm)], [f_86])).
% 42.86/29.81  tff(c_123245, plain, (![B_30]: (k3_xboole_0(B_30, B_30)=B_30)), inference(resolution, [status(thm)], [c_64, c_123241])).
% 42.86/29.81  tff(c_123077, plain, (k2_zfmisc_1('#skF_12', '#skF_11')=k2_zfmisc_1('#skF_12', '#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_123071, c_98])).
% 42.86/29.81  tff(c_125600, plain, (![A_38215, C_38216, B_38217, D_38218]: (k3_xboole_0(k2_zfmisc_1(A_38215, C_38216), k2_zfmisc_1(B_38217, D_38218))=k2_zfmisc_1(k3_xboole_0(A_38215, B_38217), k3_xboole_0(C_38216, D_38218)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 42.86/29.81  tff(c_125679, plain, (![A_38215, C_38216]: (k3_xboole_0(k2_zfmisc_1(A_38215, C_38216), k2_zfmisc_1('#skF_12', '#skF_13'))=k2_zfmisc_1(k3_xboole_0(A_38215, '#skF_12'), k3_xboole_0(C_38216, '#skF_11')))), inference(superposition, [status(thm), theory('equality')], [c_123077, c_125600])).
% 42.86/29.81  tff(c_125766, plain, (![A_38278, C_38279]: (k2_zfmisc_1(k3_xboole_0(A_38278, '#skF_12'), k3_xboole_0(C_38279, '#skF_11'))=k2_zfmisc_1(k3_xboole_0(A_38278, '#skF_12'), k3_xboole_0(C_38279, '#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_125679])).
% 42.86/29.81  tff(c_125804, plain, (![C_38279]: (k2_zfmisc_1(k3_xboole_0('#skF_12', '#skF_12'), k3_xboole_0(C_38279, '#skF_13'))=k2_zfmisc_1('#skF_12', k3_xboole_0(C_38279, '#skF_11')))), inference(superposition, [status(thm), theory('equality')], [c_123245, c_125766])).
% 42.86/29.81  tff(c_127646, plain, (![C_39127]: (k2_zfmisc_1('#skF_12', k3_xboole_0(C_39127, '#skF_11'))=k2_zfmisc_1('#skF_12', k3_xboole_0(C_39127, '#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_123245, c_125804])).
% 42.86/29.81  tff(c_127661, plain, (![C_39127]: (k3_xboole_0(C_39127, '#skF_11')=k1_xboole_0 | k1_xboole_0='#skF_12' | k2_zfmisc_1('#skF_12', k3_xboole_0(C_39127, '#skF_13'))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_127646, c_84])).
% 42.86/29.81  tff(c_129557, plain, (![C_39870]: (k3_xboole_0(C_39870, '#skF_11')=k1_xboole_0 | k2_zfmisc_1('#skF_12', k3_xboole_0(C_39870, '#skF_13'))!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_123072, c_127661])).
% 42.86/29.81  tff(c_129609, plain, (![B_2]: (k3_xboole_0(B_2, '#skF_11')=k1_xboole_0 | k2_zfmisc_1('#skF_12', k3_xboole_0('#skF_13', B_2))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_129557])).
% 42.86/29.81  tff(c_178786, plain, (![A_48733]: (k3_xboole_0(k4_xboole_0(A_48733, '#skF_13'), '#skF_11')=k1_xboole_0 | k2_zfmisc_1('#skF_12', k1_xboole_0)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_178339, c_129609])).
% 42.86/29.81  tff(c_180038, plain, (![A_48792]: (k3_xboole_0('#skF_11', k4_xboole_0(A_48792, '#skF_13'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_86, c_2, c_178786])).
% 42.86/29.81  tff(c_123351, plain, (![A_35842, B_35843]: (r2_hidden('#skF_2'(A_35842, B_35843), A_35842) | r1_tarski(A_35842, B_35843))), inference(cnfTransformation, [status(thm)], [f_40])).
% 42.86/29.81  tff(c_134468, plain, (![A_41425, B_41426, B_41427]: (r2_hidden('#skF_2'(k4_xboole_0(A_41425, B_41426), B_41427), A_41425) | r1_tarski(k4_xboole_0(A_41425, B_41426), B_41427))), inference(resolution, [status(thm)], [c_123351, c_36])).
% 42.86/29.81  tff(c_134544, plain, (![A_41456, B_41457]: (r1_tarski(k4_xboole_0(A_41456, B_41457), A_41456))), inference(resolution, [status(thm)], [c_134468, c_10])).
% 42.86/29.81  tff(c_135667, plain, (![A_41698, B_41699]: (k3_xboole_0(k4_xboole_0(A_41698, B_41699), A_41698)=k4_xboole_0(A_41698, B_41699))), inference(resolution, [status(thm)], [c_134544, c_66])).
% 42.86/29.81  tff(c_135982, plain, (![A_1, B_41699]: (k3_xboole_0(A_1, k4_xboole_0(A_1, B_41699))=k4_xboole_0(A_1, B_41699))), inference(superposition, [status(thm), theory('equality')], [c_2, c_135667])).
% 42.86/29.81  tff(c_180290, plain, (k4_xboole_0('#skF_11', '#skF_13')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_180038, c_135982])).
% 42.86/29.81  tff(c_180768, plain, (![D_23]: (r2_hidden(D_23, k1_xboole_0) | r2_hidden(D_23, '#skF_13') | ~r2_hidden(D_23, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_180290, c_32])).
% 42.86/29.81  tff(c_181952, plain, (![D_48910]: (r2_hidden(D_48910, '#skF_13') | ~r2_hidden(D_48910, '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_123423, c_180768])).
% 42.86/29.81  tff(c_193620, plain, (![B_62214]: (r2_hidden('#skF_2'('#skF_11', B_62214), '#skF_13') | r1_tarski('#skF_11', B_62214))), inference(resolution, [status(thm)], [c_12, c_181952])).
% 42.86/29.81  tff(c_193650, plain, (r1_tarski('#skF_11', '#skF_13')), inference(resolution, [status(thm)], [c_193620, c_10])).
% 42.86/29.81  tff(c_125676, plain, (![B_38217, D_38218]: (k3_xboole_0(k2_zfmisc_1('#skF_12', '#skF_13'), k2_zfmisc_1(B_38217, D_38218))=k2_zfmisc_1(k3_xboole_0('#skF_12', B_38217), k3_xboole_0('#skF_11', D_38218)))), inference(superposition, [status(thm), theory('equality')], [c_123077, c_125600])).
% 42.86/29.81  tff(c_126189, plain, (![B_38547, D_38548]: (k2_zfmisc_1(k3_xboole_0('#skF_12', B_38547), k3_xboole_0('#skF_11', D_38548))=k2_zfmisc_1(k3_xboole_0('#skF_12', B_38547), k3_xboole_0('#skF_13', D_38548)))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_125676])).
% 42.86/29.81  tff(c_126235, plain, (![D_38548]: (k2_zfmisc_1(k3_xboole_0('#skF_12', '#skF_12'), k3_xboole_0('#skF_13', D_38548))=k2_zfmisc_1('#skF_12', k3_xboole_0('#skF_11', D_38548)))), inference(superposition, [status(thm), theory('equality')], [c_123245, c_126189])).
% 42.86/29.81  tff(c_126274, plain, (![D_38548]: (k2_zfmisc_1('#skF_12', k3_xboole_0('#skF_11', D_38548))=k2_zfmisc_1('#skF_12', k3_xboole_0('#skF_13', D_38548)))), inference(demodulation, [status(thm), theory('equality')], [c_123245, c_126235])).
% 42.86/29.81  tff(c_178824, plain, (![A_48733]: (k2_zfmisc_1('#skF_12', k3_xboole_0('#skF_13', k4_xboole_0(A_48733, '#skF_11')))=k2_zfmisc_1('#skF_12', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_178339, c_126274])).
% 42.86/29.81  tff(c_184343, plain, (![A_49500]: (k2_zfmisc_1('#skF_12', k3_xboole_0('#skF_13', k4_xboole_0(A_49500, '#skF_11')))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_86, c_178824])).
% 42.86/29.81  tff(c_127214, plain, (![B_39005, B_39006]: (k2_zfmisc_1(k3_xboole_0('#skF_12', B_39005), k3_xboole_0(B_39006, '#skF_11'))=k2_zfmisc_1(k3_xboole_0('#skF_12', B_39005), k3_xboole_0('#skF_13', B_39006)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_126189])).
% 42.86/29.81  tff(c_125690, plain, (![A_38215, C_38216]: (k2_zfmisc_1(k3_xboole_0(A_38215, '#skF_12'), k3_xboole_0(C_38216, '#skF_11'))=k2_zfmisc_1(k3_xboole_0(A_38215, '#skF_12'), k3_xboole_0(C_38216, '#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_125679])).
% 42.86/29.81  tff(c_127232, plain, (![B_39006]: (k2_zfmisc_1(k3_xboole_0('#skF_12', '#skF_12'), k3_xboole_0(B_39006, '#skF_13'))=k2_zfmisc_1(k3_xboole_0('#skF_12', '#skF_12'), k3_xboole_0('#skF_13', B_39006)))), inference(superposition, [status(thm), theory('equality')], [c_127214, c_125690])).
% 42.86/29.81  tff(c_128984, plain, (![B_39691]: (k2_zfmisc_1('#skF_12', k3_xboole_0(B_39691, '#skF_13'))=k2_zfmisc_1('#skF_12', k3_xboole_0('#skF_13', B_39691)))), inference(demodulation, [status(thm), theory('equality')], [c_123245, c_123245, c_127232])).
% 42.86/29.81  tff(c_129019, plain, (![B_39691]: (k3_xboole_0('#skF_13', B_39691)=k1_xboole_0 | k1_xboole_0='#skF_12' | k2_zfmisc_1('#skF_12', k3_xboole_0(B_39691, '#skF_13'))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_128984, c_84])).
% 42.86/29.81  tff(c_129649, plain, (![B_39930]: (k3_xboole_0('#skF_13', B_39930)=k1_xboole_0 | k2_zfmisc_1('#skF_12', k3_xboole_0(B_39930, '#skF_13'))!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_123072, c_129019])).
% 42.86/29.81  tff(c_129701, plain, (![B_2]: (k3_xboole_0('#skF_13', B_2)=k1_xboole_0 | k2_zfmisc_1('#skF_12', k3_xboole_0('#skF_13', B_2))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_129649])).
% 42.86/29.81  tff(c_184450, plain, (![A_49529]: (k3_xboole_0('#skF_13', k4_xboole_0(A_49529, '#skF_11'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_184343, c_129701])).
% 42.86/29.81  tff(c_184738, plain, (k4_xboole_0('#skF_13', '#skF_11')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_184450, c_135982])).
% 42.86/29.81  tff(c_185235, plain, (![D_23]: (r2_hidden(D_23, k1_xboole_0) | r2_hidden(D_23, '#skF_11') | ~r2_hidden(D_23, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_184738, c_32])).
% 42.86/29.81  tff(c_185959, plain, (![D_49615]: (r2_hidden(D_49615, '#skF_11') | ~r2_hidden(D_49615, '#skF_13'))), inference(negUnitSimplification, [status(thm)], [c_123423, c_185235])).
% 42.86/29.81  tff(c_197233, plain, (![B_63482]: (~r2_xboole_0('#skF_11', B_63482) | ~r2_hidden('#skF_7'('#skF_11', B_63482), '#skF_13'))), inference(resolution, [status(thm)], [c_185959, c_56])).
% 42.86/29.81  tff(c_197273, plain, (~r2_xboole_0('#skF_11', '#skF_13')), inference(resolution, [status(thm)], [c_58, c_197233])).
% 42.86/29.81  tff(c_197276, plain, ('#skF_11'='#skF_13' | ~r1_tarski('#skF_11', '#skF_13')), inference(resolution, [status(thm)], [c_50, c_197273])).
% 42.86/29.81  tff(c_197279, plain, ('#skF_11'='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_193650, c_197276])).
% 42.86/29.81  tff(c_197281, plain, $false, inference(negUnitSimplification, [status(thm)], [c_123070, c_197279])).
% 42.86/29.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 42.86/29.81  
% 42.86/29.81  Inference rules
% 42.86/29.81  ----------------------
% 42.86/29.81  #Ref     : 0
% 42.86/29.81  #Sup     : 49352
% 42.86/29.81  #Fact    : 14
% 42.86/29.81  #Define  : 0
% 42.86/29.81  #Split   : 27
% 42.86/29.81  #Chain   : 0
% 42.86/29.81  #Close   : 0
% 42.86/29.81  
% 42.86/29.81  Ordering : KBO
% 42.86/29.81  
% 42.86/29.81  Simplification rules
% 42.86/29.81  ----------------------
% 42.86/29.81  #Subsume      : 19434
% 42.86/29.81  #Demod        : 30593
% 42.86/29.81  #Tautology    : 9259
% 42.86/29.81  #SimpNegUnit  : 1409
% 42.86/29.81  #BackRed      : 379
% 42.86/29.81  
% 42.86/29.81  #Partial instantiations: 39204
% 42.86/29.81  #Strategies tried      : 1
% 42.86/29.81  
% 42.86/29.81  Timing (in seconds)
% 42.86/29.81  ----------------------
% 42.86/29.81  Preprocessing        : 0.33
% 42.86/29.81  Parsing              : 0.17
% 42.86/29.81  CNF conversion       : 0.03
% 42.86/29.81  Main loop            : 28.68
% 42.86/29.81  Inferencing          : 4.28
% 42.86/29.81  Reduction            : 11.93
% 42.86/29.81  Demodulation         : 9.96
% 42.86/29.81  BG Simplification    : 0.50
% 42.86/29.81  Subsumption          : 10.49
% 42.86/29.81  Abstraction          : 0.81
% 42.86/29.81  MUC search           : 0.00
% 42.86/29.81  Cooper               : 0.00
% 42.86/29.81  Total                : 29.07
% 42.86/29.81  Index Insertion      : 0.00
% 42.86/29.81  Index Deletion       : 0.00
% 42.86/29.81  Index Matching       : 0.00
% 42.86/29.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
