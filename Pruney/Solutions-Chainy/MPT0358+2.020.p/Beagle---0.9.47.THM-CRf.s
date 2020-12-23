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
% DateTime   : Thu Dec  3 09:56:02 EST 2020

% Result     : Theorem 8.83s
% Output     : CNFRefutation 9.07s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 949 expanded)
%              Number of leaves         :   31 ( 325 expanded)
%              Depth                    :   20
%              Number of atoms          :  197 (1756 expanded)
%              Number of equality atoms :   49 ( 491 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_71,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_78,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_48,plain,(
    ! [A_23] : k1_subset_1(A_23) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_56,plain,
    ( k1_subset_1('#skF_4') != '#skF_5'
    | ~ r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_64,plain,
    ( k1_xboole_0 != '#skF_5'
    | ~ r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_56])).

tff(c_126,plain,(
    ~ r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_52,plain,(
    ! [A_26] : ~ v1_xboole_0(k1_zfmisc_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_156,plain,(
    ! [B_44,A_45] :
      ( r2_hidden(B_44,A_45)
      | ~ m1_subset_1(B_44,A_45)
      | v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_28,plain,(
    ! [C_20,A_16] :
      ( r1_tarski(C_20,A_16)
      | ~ r2_hidden(C_20,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_160,plain,(
    ! [B_44,A_16] :
      ( r1_tarski(B_44,A_16)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_16))
      | v1_xboole_0(k1_zfmisc_1(A_16)) ) ),
    inference(resolution,[status(thm)],[c_156,c_28])).

tff(c_164,plain,(
    ! [B_46,A_47] :
      ( r1_tarski(B_46,A_47)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_160])).

tff(c_173,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_164])).

tff(c_62,plain,
    ( r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5'))
    | k1_subset_1('#skF_4') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_63,plain,
    ( r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5'))
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_62])).

tff(c_127,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_26,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_128,plain,(
    ! [A_15] : k5_xboole_0(A_15,'#skF_5') = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_26])).

tff(c_24,plain,(
    ! [A_13,B_14] :
      ( k3_xboole_0(A_13,B_14) = A_13
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_177,plain,(
    k3_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_173,c_24])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_181,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_2])).

tff(c_201,plain,(
    ! [A_48,B_49] : k5_xboole_0(A_48,k3_xboole_0(A_48,B_49)) = k4_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_210,plain,(
    k5_xboole_0('#skF_4','#skF_5') = k4_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_201])).

tff(c_222,plain,(
    k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_210])).

tff(c_367,plain,(
    ! [A_66,B_67] :
      ( k4_xboole_0(A_66,B_67) = k3_subset_1(A_66,B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_377,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k3_subset_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_367])).

tff(c_381,plain,(
    k3_subset_1('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_377])).

tff(c_382,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_381,c_126])).

tff(c_385,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_382])).

tff(c_386,plain,(
    r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_388,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_386])).

tff(c_389,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_633,plain,(
    ! [A_94,B_95] :
      ( k4_xboole_0(A_94,B_95) = k3_subset_1(A_94,B_95)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_646,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k3_subset_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_633])).

tff(c_407,plain,(
    ! [B_72,A_73] :
      ( r2_hidden(B_72,A_73)
      | ~ m1_subset_1(B_72,A_73)
      | v1_xboole_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_411,plain,(
    ! [B_72,A_16] :
      ( r1_tarski(B_72,A_16)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_16))
      | v1_xboole_0(k1_zfmisc_1(A_16)) ) ),
    inference(resolution,[status(thm)],[c_407,c_28])).

tff(c_415,plain,(
    ! [B_74,A_75] :
      ( r1_tarski(B_74,A_75)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_75)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_411])).

tff(c_424,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_415])).

tff(c_428,plain,(
    k3_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_424,c_24])).

tff(c_432,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_428,c_2])).

tff(c_512,plain,(
    ! [A_86,B_87] : k5_xboole_0(A_86,k3_xboole_0(A_86,B_87)) = k4_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_524,plain,(
    k5_xboole_0('#skF_4','#skF_5') = k4_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_512])).

tff(c_647,plain,(
    k5_xboole_0('#skF_4','#skF_5') = k3_subset_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_646,c_524])).

tff(c_827,plain,(
    ! [A_114,B_115,C_116] :
      ( r2_hidden(A_114,B_115)
      | r2_hidden(A_114,C_116)
      | ~ r2_hidden(A_114,k5_xboole_0(B_115,C_116)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6754,plain,(
    ! [B_401,C_402,B_403] :
      ( r2_hidden('#skF_1'(k5_xboole_0(B_401,C_402),B_403),B_401)
      | r2_hidden('#skF_1'(k5_xboole_0(B_401,C_402),B_403),C_402)
      | r1_tarski(k5_xboole_0(B_401,C_402),B_403) ) ),
    inference(resolution,[status(thm)],[c_8,c_827])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_8814,plain,(
    ! [B_436,C_437] :
      ( r2_hidden('#skF_1'(k5_xboole_0(B_436,C_437),B_436),C_437)
      | r1_tarski(k5_xboole_0(B_436,C_437),B_436) ) ),
    inference(resolution,[status(thm)],[c_6754,c_6])).

tff(c_8942,plain,
    ( r2_hidden('#skF_1'(k3_subset_1('#skF_4','#skF_5'),'#skF_4'),'#skF_5')
    | r1_tarski(k5_xboole_0('#skF_4','#skF_5'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_647,c_8814])).

tff(c_8999,plain,
    ( r2_hidden('#skF_1'(k3_subset_1('#skF_4','#skF_5'),'#skF_4'),'#skF_5')
    | r1_tarski(k3_subset_1('#skF_4','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_647,c_8942])).

tff(c_11556,plain,(
    r1_tarski(k3_subset_1('#skF_4','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_8999])).

tff(c_881,plain,(
    ! [A_118,B_119,C_120] :
      ( r2_hidden(A_118,B_119)
      | ~ r2_hidden(A_118,C_120)
      | r2_hidden(A_118,k5_xboole_0(B_119,C_120)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1328,plain,(
    ! [A_151] :
      ( r2_hidden(A_151,'#skF_4')
      | ~ r2_hidden(A_151,'#skF_5')
      | r2_hidden(A_151,k3_subset_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_647,c_881])).

tff(c_4,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1351,plain,(
    ! [A_151,B_4] :
      ( r2_hidden(A_151,B_4)
      | ~ r1_tarski(k3_subset_1('#skF_4','#skF_5'),B_4)
      | r2_hidden(A_151,'#skF_4')
      | ~ r2_hidden(A_151,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1328,c_4])).

tff(c_11627,plain,(
    ! [A_474] :
      ( r2_hidden(A_474,'#skF_4')
      | ~ r2_hidden(A_474,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_11556,c_1351])).

tff(c_11716,plain,(
    ! [B_4] :
      ( r2_hidden('#skF_1'('#skF_5',B_4),'#skF_4')
      | r1_tarski('#skF_5',B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_11627])).

tff(c_721,plain,(
    ! [A_100,C_101,B_102] :
      ( r2_hidden(A_100,C_101)
      | ~ r2_hidden(A_100,B_102)
      | r2_hidden(A_100,k5_xboole_0(B_102,C_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8294,plain,(
    ! [A_428,B_429,C_430] :
      ( r1_tarski(A_428,k5_xboole_0(B_429,C_430))
      | r2_hidden('#skF_1'(A_428,k5_xboole_0(B_429,C_430)),C_430)
      | ~ r2_hidden('#skF_1'(A_428,k5_xboole_0(B_429,C_430)),B_429) ) ),
    inference(resolution,[status(thm)],[c_721,c_6])).

tff(c_8523,plain,(
    ! [A_431,C_432] :
      ( r2_hidden('#skF_1'(A_431,k5_xboole_0(A_431,C_432)),C_432)
      | r1_tarski(A_431,k5_xboole_0(A_431,C_432)) ) ),
    inference(resolution,[status(thm)],[c_8,c_8294])).

tff(c_8639,plain,
    ( r2_hidden('#skF_1'('#skF_4',k3_subset_1('#skF_4','#skF_5')),'#skF_5')
    | r1_tarski('#skF_4',k5_xboole_0('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_647,c_8523])).

tff(c_8691,plain,
    ( r2_hidden('#skF_1'('#skF_4',k3_subset_1('#skF_4','#skF_5')),'#skF_5')
    | r1_tarski('#skF_4',k3_subset_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_647,c_8639])).

tff(c_11206,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_8691])).

tff(c_11220,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_4','#skF_5')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_11206,c_24])).

tff(c_11581,plain,(
    k3_xboole_0(k3_subset_1('#skF_4','#skF_5'),'#skF_4') = k3_subset_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_11556,c_24])).

tff(c_11740,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_4','#skF_5')) = k3_subset_1('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_11581,c_2])).

tff(c_11758,plain,(
    k3_subset_1('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11220,c_11740])).

tff(c_390,plain,(
    r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_30,plain,(
    ! [C_20,A_16] :
      ( r2_hidden(C_20,k1_zfmisc_1(A_16))
      | ~ r1_tarski(C_20,A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_458,plain,(
    ! [B_78,A_79] :
      ( m1_subset_1(B_78,A_79)
      | ~ r2_hidden(B_78,A_79)
      | v1_xboole_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_467,plain,(
    ! [C_20,A_16] :
      ( m1_subset_1(C_20,k1_zfmisc_1(A_16))
      | v1_xboole_0(k1_zfmisc_1(A_16))
      | ~ r1_tarski(C_20,A_16) ) ),
    inference(resolution,[status(thm)],[c_30,c_458])).

tff(c_472,plain,(
    ! [C_20,A_16] :
      ( m1_subset_1(C_20,k1_zfmisc_1(A_16))
      | ~ r1_tarski(C_20,A_16) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_467])).

tff(c_665,plain,(
    ! [A_96,C_97] :
      ( k4_xboole_0(A_96,C_97) = k3_subset_1(A_96,C_97)
      | ~ r1_tarski(C_97,A_96) ) ),
    inference(resolution,[status(thm)],[c_472,c_633])).

tff(c_678,plain,(
    k4_xboole_0(k3_subset_1('#skF_4','#skF_5'),'#skF_5') = k3_subset_1(k3_subset_1('#skF_4','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_390,c_665])).

tff(c_398,plain,(
    ! [A_70,B_71] :
      ( k3_xboole_0(A_70,B_71) = A_70
      | ~ r1_tarski(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_402,plain,(
    k3_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_390,c_398])).

tff(c_590,plain,(
    ! [A_92,B_93] : k5_xboole_0(A_92,k3_xboole_0(B_93,A_92)) = k4_xboole_0(A_92,B_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_512])).

tff(c_616,plain,(
    k5_xboole_0(k3_subset_1('#skF_4','#skF_5'),'#skF_5') = k4_xboole_0(k3_subset_1('#skF_4','#skF_5'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_590])).

tff(c_762,plain,(
    k5_xboole_0(k3_subset_1('#skF_4','#skF_5'),'#skF_5') = k3_subset_1(k3_subset_1('#skF_4','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_678,c_616])).

tff(c_1001,plain,(
    ! [A_127,C_128,B_129] :
      ( ~ r2_hidden(A_127,C_128)
      | ~ r2_hidden(A_127,B_129)
      | ~ r2_hidden(A_127,k5_xboole_0(B_129,C_128)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1007,plain,(
    ! [A_127] :
      ( ~ r2_hidden(A_127,'#skF_5')
      | ~ r2_hidden(A_127,k3_subset_1('#skF_4','#skF_5'))
      | ~ r2_hidden(A_127,k3_subset_1(k3_subset_1('#skF_4','#skF_5'),'#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_762,c_1001])).

tff(c_12055,plain,(
    ! [A_480] :
      ( ~ r2_hidden(A_480,'#skF_5')
      | ~ r2_hidden(A_480,'#skF_4')
      | ~ r2_hidden(A_480,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11758,c_11758,c_11758,c_1007])).

tff(c_12136,plain,(
    ! [B_481] :
      ( ~ r2_hidden('#skF_1'('#skF_5',B_481),'#skF_4')
      | r1_tarski('#skF_5',B_481) ) ),
    inference(resolution,[status(thm)],[c_8,c_12055])).

tff(c_12203,plain,(
    ! [B_484] : r1_tarski('#skF_5',B_484) ),
    inference(resolution,[status(thm)],[c_11716,c_12136])).

tff(c_12235,plain,(
    ! [B_485] : k3_xboole_0('#skF_5',B_485) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_12203,c_24])).

tff(c_916,plain,(
    ! [A_121,A_122] :
      ( r2_hidden(A_121,A_122)
      | ~ r2_hidden(A_121,k1_xboole_0)
      | r2_hidden(A_121,A_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_881])).

tff(c_925,plain,(
    ! [B_123,A_124] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_123),A_124)
      | r1_tarski(k1_xboole_0,B_123) ) ),
    inference(resolution,[status(thm)],[c_8,c_916])).

tff(c_953,plain,(
    ! [A_125] : r1_tarski(k1_xboole_0,A_125) ),
    inference(resolution,[status(thm)],[c_925,c_6])).

tff(c_962,plain,(
    ! [A_126] : k3_xboole_0(k1_xboole_0,A_126) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_953,c_24])).

tff(c_994,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_962])).

tff(c_12257,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_12235,c_994])).

tff(c_12303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_389,c_12257])).

tff(c_12305,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_8999])).

tff(c_12304,plain,(
    r2_hidden('#skF_1'(k3_subset_1('#skF_4','#skF_5'),'#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_8999])).

tff(c_12315,plain,(
    ! [B_486] :
      ( r2_hidden('#skF_1'(k3_subset_1('#skF_4','#skF_5'),'#skF_4'),B_486)
      | ~ r1_tarski('#skF_5',B_486) ) ),
    inference(resolution,[status(thm)],[c_12304,c_4])).

tff(c_12402,plain,
    ( r1_tarski(k3_subset_1('#skF_4','#skF_5'),'#skF_4')
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_12315,c_6])).

tff(c_12444,plain,(
    r1_tarski(k3_subset_1('#skF_4','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_424,c_12402])).

tff(c_12446,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12305,c_12444])).

tff(c_12448,plain,(
    ~ r1_tarski('#skF_4',k3_subset_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_8691])).

tff(c_12447,plain,(
    r2_hidden('#skF_1'('#skF_4',k3_subset_1('#skF_4','#skF_5')),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_8691])).

tff(c_12542,plain,(
    ! [B_490] :
      ( r2_hidden('#skF_1'('#skF_4',k3_subset_1('#skF_4','#skF_5')),B_490)
      | ~ r1_tarski('#skF_5',B_490) ) ),
    inference(resolution,[status(thm)],[c_12447,c_4])).

tff(c_12633,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_4','#skF_5'))
    | ~ r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_12542,c_6])).

tff(c_12678,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_12633])).

tff(c_12680,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12448,c_12678])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:35:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.83/3.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.07/3.31  
% 9.07/3.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.07/3.31  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 9.07/3.31  
% 9.07/3.31  %Foreground sorts:
% 9.07/3.31  
% 9.07/3.31  
% 9.07/3.31  %Background operators:
% 9.07/3.31  
% 9.07/3.31  
% 9.07/3.31  %Foreground operators:
% 9.07/3.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.07/3.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.07/3.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.07/3.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.07/3.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.07/3.31  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.07/3.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.07/3.31  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 9.07/3.31  tff('#skF_5', type, '#skF_5': $i).
% 9.07/3.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.07/3.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.07/3.31  tff('#skF_4', type, '#skF_4': $i).
% 9.07/3.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.07/3.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.07/3.31  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 9.07/3.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.07/3.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.07/3.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.07/3.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.07/3.31  
% 9.07/3.33  tff(f_71, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 9.07/3.33  tff(f_85, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 9.07/3.33  tff(f_78, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 9.07/3.33  tff(f_69, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 9.07/3.33  tff(f_56, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 9.07/3.33  tff(f_49, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 9.07/3.33  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.07/3.33  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.07/3.33  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.07/3.33  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 9.07/3.33  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 9.07/3.33  tff(f_41, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 9.07/3.33  tff(c_48, plain, (![A_23]: (k1_subset_1(A_23)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.07/3.33  tff(c_56, plain, (k1_subset_1('#skF_4')!='#skF_5' | ~r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.07/3.33  tff(c_64, plain, (k1_xboole_0!='#skF_5' | ~r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_56])).
% 9.07/3.33  tff(c_126, plain, (~r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_64])).
% 9.07/3.33  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.07/3.33  tff(c_52, plain, (![A_26]: (~v1_xboole_0(k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.07/3.33  tff(c_156, plain, (![B_44, A_45]: (r2_hidden(B_44, A_45) | ~m1_subset_1(B_44, A_45) | v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.07/3.33  tff(c_28, plain, (![C_20, A_16]: (r1_tarski(C_20, A_16) | ~r2_hidden(C_20, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.07/3.33  tff(c_160, plain, (![B_44, A_16]: (r1_tarski(B_44, A_16) | ~m1_subset_1(B_44, k1_zfmisc_1(A_16)) | v1_xboole_0(k1_zfmisc_1(A_16)))), inference(resolution, [status(thm)], [c_156, c_28])).
% 9.07/3.33  tff(c_164, plain, (![B_46, A_47]: (r1_tarski(B_46, A_47) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)))), inference(negUnitSimplification, [status(thm)], [c_52, c_160])).
% 9.07/3.33  tff(c_173, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_54, c_164])).
% 9.07/3.33  tff(c_62, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5')) | k1_subset_1('#skF_4')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.07/3.33  tff(c_63, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5')) | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_62])).
% 9.07/3.33  tff(c_127, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_63])).
% 9.07/3.33  tff(c_26, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.07/3.33  tff(c_128, plain, (![A_15]: (k5_xboole_0(A_15, '#skF_5')=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_127, c_26])).
% 9.07/3.33  tff(c_24, plain, (![A_13, B_14]: (k3_xboole_0(A_13, B_14)=A_13 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.07/3.33  tff(c_177, plain, (k3_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_173, c_24])).
% 9.07/3.33  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.07/3.33  tff(c_181, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_177, c_2])).
% 9.07/3.33  tff(c_201, plain, (![A_48, B_49]: (k5_xboole_0(A_48, k3_xboole_0(A_48, B_49))=k4_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.07/3.33  tff(c_210, plain, (k5_xboole_0('#skF_4', '#skF_5')=k4_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_181, c_201])).
% 9.07/3.33  tff(c_222, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_128, c_210])).
% 9.07/3.33  tff(c_367, plain, (![A_66, B_67]: (k4_xboole_0(A_66, B_67)=k3_subset_1(A_66, B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.07/3.33  tff(c_377, plain, (k4_xboole_0('#skF_4', '#skF_5')=k3_subset_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_367])).
% 9.07/3.33  tff(c_381, plain, (k3_subset_1('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_222, c_377])).
% 9.07/3.33  tff(c_382, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_381, c_126])).
% 9.07/3.33  tff(c_385, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_173, c_382])).
% 9.07/3.33  tff(c_386, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_63])).
% 9.07/3.33  tff(c_388, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126, c_386])).
% 9.07/3.33  tff(c_389, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_64])).
% 9.07/3.33  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.07/3.33  tff(c_633, plain, (![A_94, B_95]: (k4_xboole_0(A_94, B_95)=k3_subset_1(A_94, B_95) | ~m1_subset_1(B_95, k1_zfmisc_1(A_94)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.07/3.33  tff(c_646, plain, (k4_xboole_0('#skF_4', '#skF_5')=k3_subset_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_633])).
% 9.07/3.33  tff(c_407, plain, (![B_72, A_73]: (r2_hidden(B_72, A_73) | ~m1_subset_1(B_72, A_73) | v1_xboole_0(A_73))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.07/3.33  tff(c_411, plain, (![B_72, A_16]: (r1_tarski(B_72, A_16) | ~m1_subset_1(B_72, k1_zfmisc_1(A_16)) | v1_xboole_0(k1_zfmisc_1(A_16)))), inference(resolution, [status(thm)], [c_407, c_28])).
% 9.07/3.33  tff(c_415, plain, (![B_74, A_75]: (r1_tarski(B_74, A_75) | ~m1_subset_1(B_74, k1_zfmisc_1(A_75)))), inference(negUnitSimplification, [status(thm)], [c_52, c_411])).
% 9.07/3.33  tff(c_424, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_54, c_415])).
% 9.07/3.33  tff(c_428, plain, (k3_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_424, c_24])).
% 9.07/3.33  tff(c_432, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_428, c_2])).
% 9.07/3.33  tff(c_512, plain, (![A_86, B_87]: (k5_xboole_0(A_86, k3_xboole_0(A_86, B_87))=k4_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.07/3.33  tff(c_524, plain, (k5_xboole_0('#skF_4', '#skF_5')=k4_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_432, c_512])).
% 9.07/3.33  tff(c_647, plain, (k5_xboole_0('#skF_4', '#skF_5')=k3_subset_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_646, c_524])).
% 9.07/3.33  tff(c_827, plain, (![A_114, B_115, C_116]: (r2_hidden(A_114, B_115) | r2_hidden(A_114, C_116) | ~r2_hidden(A_114, k5_xboole_0(B_115, C_116)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.07/3.33  tff(c_6754, plain, (![B_401, C_402, B_403]: (r2_hidden('#skF_1'(k5_xboole_0(B_401, C_402), B_403), B_401) | r2_hidden('#skF_1'(k5_xboole_0(B_401, C_402), B_403), C_402) | r1_tarski(k5_xboole_0(B_401, C_402), B_403))), inference(resolution, [status(thm)], [c_8, c_827])).
% 9.07/3.33  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.07/3.33  tff(c_8814, plain, (![B_436, C_437]: (r2_hidden('#skF_1'(k5_xboole_0(B_436, C_437), B_436), C_437) | r1_tarski(k5_xboole_0(B_436, C_437), B_436))), inference(resolution, [status(thm)], [c_6754, c_6])).
% 9.07/3.33  tff(c_8942, plain, (r2_hidden('#skF_1'(k3_subset_1('#skF_4', '#skF_5'), '#skF_4'), '#skF_5') | r1_tarski(k5_xboole_0('#skF_4', '#skF_5'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_647, c_8814])).
% 9.07/3.33  tff(c_8999, plain, (r2_hidden('#skF_1'(k3_subset_1('#skF_4', '#skF_5'), '#skF_4'), '#skF_5') | r1_tarski(k3_subset_1('#skF_4', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_647, c_8942])).
% 9.07/3.33  tff(c_11556, plain, (r1_tarski(k3_subset_1('#skF_4', '#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_8999])).
% 9.07/3.33  tff(c_881, plain, (![A_118, B_119, C_120]: (r2_hidden(A_118, B_119) | ~r2_hidden(A_118, C_120) | r2_hidden(A_118, k5_xboole_0(B_119, C_120)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.07/3.33  tff(c_1328, plain, (![A_151]: (r2_hidden(A_151, '#skF_4') | ~r2_hidden(A_151, '#skF_5') | r2_hidden(A_151, k3_subset_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_647, c_881])).
% 9.07/3.33  tff(c_4, plain, (![C_7, B_4, A_3]: (r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.07/3.33  tff(c_1351, plain, (![A_151, B_4]: (r2_hidden(A_151, B_4) | ~r1_tarski(k3_subset_1('#skF_4', '#skF_5'), B_4) | r2_hidden(A_151, '#skF_4') | ~r2_hidden(A_151, '#skF_5'))), inference(resolution, [status(thm)], [c_1328, c_4])).
% 9.07/3.33  tff(c_11627, plain, (![A_474]: (r2_hidden(A_474, '#skF_4') | ~r2_hidden(A_474, '#skF_5'))), inference(resolution, [status(thm)], [c_11556, c_1351])).
% 9.07/3.33  tff(c_11716, plain, (![B_4]: (r2_hidden('#skF_1'('#skF_5', B_4), '#skF_4') | r1_tarski('#skF_5', B_4))), inference(resolution, [status(thm)], [c_8, c_11627])).
% 9.07/3.33  tff(c_721, plain, (![A_100, C_101, B_102]: (r2_hidden(A_100, C_101) | ~r2_hidden(A_100, B_102) | r2_hidden(A_100, k5_xboole_0(B_102, C_101)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.07/3.33  tff(c_8294, plain, (![A_428, B_429, C_430]: (r1_tarski(A_428, k5_xboole_0(B_429, C_430)) | r2_hidden('#skF_1'(A_428, k5_xboole_0(B_429, C_430)), C_430) | ~r2_hidden('#skF_1'(A_428, k5_xboole_0(B_429, C_430)), B_429))), inference(resolution, [status(thm)], [c_721, c_6])).
% 9.07/3.33  tff(c_8523, plain, (![A_431, C_432]: (r2_hidden('#skF_1'(A_431, k5_xboole_0(A_431, C_432)), C_432) | r1_tarski(A_431, k5_xboole_0(A_431, C_432)))), inference(resolution, [status(thm)], [c_8, c_8294])).
% 9.07/3.33  tff(c_8639, plain, (r2_hidden('#skF_1'('#skF_4', k3_subset_1('#skF_4', '#skF_5')), '#skF_5') | r1_tarski('#skF_4', k5_xboole_0('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_647, c_8523])).
% 9.07/3.33  tff(c_8691, plain, (r2_hidden('#skF_1'('#skF_4', k3_subset_1('#skF_4', '#skF_5')), '#skF_5') | r1_tarski('#skF_4', k3_subset_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_647, c_8639])).
% 9.07/3.33  tff(c_11206, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_8691])).
% 9.07/3.33  tff(c_11220, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_4', '#skF_5'))='#skF_4'), inference(resolution, [status(thm)], [c_11206, c_24])).
% 9.07/3.33  tff(c_11581, plain, (k3_xboole_0(k3_subset_1('#skF_4', '#skF_5'), '#skF_4')=k3_subset_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_11556, c_24])).
% 9.07/3.33  tff(c_11740, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_4', '#skF_5'))=k3_subset_1('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_11581, c_2])).
% 9.07/3.33  tff(c_11758, plain, (k3_subset_1('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11220, c_11740])).
% 9.07/3.33  tff(c_390, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_64])).
% 9.07/3.33  tff(c_30, plain, (![C_20, A_16]: (r2_hidden(C_20, k1_zfmisc_1(A_16)) | ~r1_tarski(C_20, A_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.07/3.33  tff(c_458, plain, (![B_78, A_79]: (m1_subset_1(B_78, A_79) | ~r2_hidden(B_78, A_79) | v1_xboole_0(A_79))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.07/3.33  tff(c_467, plain, (![C_20, A_16]: (m1_subset_1(C_20, k1_zfmisc_1(A_16)) | v1_xboole_0(k1_zfmisc_1(A_16)) | ~r1_tarski(C_20, A_16))), inference(resolution, [status(thm)], [c_30, c_458])).
% 9.07/3.33  tff(c_472, plain, (![C_20, A_16]: (m1_subset_1(C_20, k1_zfmisc_1(A_16)) | ~r1_tarski(C_20, A_16))), inference(negUnitSimplification, [status(thm)], [c_52, c_467])).
% 9.07/3.33  tff(c_665, plain, (![A_96, C_97]: (k4_xboole_0(A_96, C_97)=k3_subset_1(A_96, C_97) | ~r1_tarski(C_97, A_96))), inference(resolution, [status(thm)], [c_472, c_633])).
% 9.07/3.33  tff(c_678, plain, (k4_xboole_0(k3_subset_1('#skF_4', '#skF_5'), '#skF_5')=k3_subset_1(k3_subset_1('#skF_4', '#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_390, c_665])).
% 9.07/3.33  tff(c_398, plain, (![A_70, B_71]: (k3_xboole_0(A_70, B_71)=A_70 | ~r1_tarski(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.07/3.33  tff(c_402, plain, (k3_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_390, c_398])).
% 9.07/3.33  tff(c_590, plain, (![A_92, B_93]: (k5_xboole_0(A_92, k3_xboole_0(B_93, A_92))=k4_xboole_0(A_92, B_93))), inference(superposition, [status(thm), theory('equality')], [c_2, c_512])).
% 9.07/3.33  tff(c_616, plain, (k5_xboole_0(k3_subset_1('#skF_4', '#skF_5'), '#skF_5')=k4_xboole_0(k3_subset_1('#skF_4', '#skF_5'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_402, c_590])).
% 9.07/3.33  tff(c_762, plain, (k5_xboole_0(k3_subset_1('#skF_4', '#skF_5'), '#skF_5')=k3_subset_1(k3_subset_1('#skF_4', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_678, c_616])).
% 9.07/3.33  tff(c_1001, plain, (![A_127, C_128, B_129]: (~r2_hidden(A_127, C_128) | ~r2_hidden(A_127, B_129) | ~r2_hidden(A_127, k5_xboole_0(B_129, C_128)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.07/3.33  tff(c_1007, plain, (![A_127]: (~r2_hidden(A_127, '#skF_5') | ~r2_hidden(A_127, k3_subset_1('#skF_4', '#skF_5')) | ~r2_hidden(A_127, k3_subset_1(k3_subset_1('#skF_4', '#skF_5'), '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_762, c_1001])).
% 9.07/3.33  tff(c_12055, plain, (![A_480]: (~r2_hidden(A_480, '#skF_5') | ~r2_hidden(A_480, '#skF_4') | ~r2_hidden(A_480, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11758, c_11758, c_11758, c_1007])).
% 9.07/3.33  tff(c_12136, plain, (![B_481]: (~r2_hidden('#skF_1'('#skF_5', B_481), '#skF_4') | r1_tarski('#skF_5', B_481))), inference(resolution, [status(thm)], [c_8, c_12055])).
% 9.07/3.33  tff(c_12203, plain, (![B_484]: (r1_tarski('#skF_5', B_484))), inference(resolution, [status(thm)], [c_11716, c_12136])).
% 9.07/3.33  tff(c_12235, plain, (![B_485]: (k3_xboole_0('#skF_5', B_485)='#skF_5')), inference(resolution, [status(thm)], [c_12203, c_24])).
% 9.07/3.33  tff(c_916, plain, (![A_121, A_122]: (r2_hidden(A_121, A_122) | ~r2_hidden(A_121, k1_xboole_0) | r2_hidden(A_121, A_122))), inference(superposition, [status(thm), theory('equality')], [c_26, c_881])).
% 9.07/3.33  tff(c_925, plain, (![B_123, A_124]: (r2_hidden('#skF_1'(k1_xboole_0, B_123), A_124) | r1_tarski(k1_xboole_0, B_123))), inference(resolution, [status(thm)], [c_8, c_916])).
% 9.07/3.33  tff(c_953, plain, (![A_125]: (r1_tarski(k1_xboole_0, A_125))), inference(resolution, [status(thm)], [c_925, c_6])).
% 9.07/3.33  tff(c_962, plain, (![A_126]: (k3_xboole_0(k1_xboole_0, A_126)=k1_xboole_0)), inference(resolution, [status(thm)], [c_953, c_24])).
% 9.07/3.33  tff(c_994, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_962])).
% 9.07/3.33  tff(c_12257, plain, (k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_12235, c_994])).
% 9.07/3.33  tff(c_12303, plain, $false, inference(negUnitSimplification, [status(thm)], [c_389, c_12257])).
% 9.07/3.33  tff(c_12305, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_8999])).
% 9.07/3.33  tff(c_12304, plain, (r2_hidden('#skF_1'(k3_subset_1('#skF_4', '#skF_5'), '#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_8999])).
% 9.07/3.33  tff(c_12315, plain, (![B_486]: (r2_hidden('#skF_1'(k3_subset_1('#skF_4', '#skF_5'), '#skF_4'), B_486) | ~r1_tarski('#skF_5', B_486))), inference(resolution, [status(thm)], [c_12304, c_4])).
% 9.07/3.33  tff(c_12402, plain, (r1_tarski(k3_subset_1('#skF_4', '#skF_5'), '#skF_4') | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_12315, c_6])).
% 9.07/3.33  tff(c_12444, plain, (r1_tarski(k3_subset_1('#skF_4', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_424, c_12402])).
% 9.07/3.33  tff(c_12446, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12305, c_12444])).
% 9.07/3.33  tff(c_12448, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_8691])).
% 9.07/3.33  tff(c_12447, plain, (r2_hidden('#skF_1'('#skF_4', k3_subset_1('#skF_4', '#skF_5')), '#skF_5')), inference(splitRight, [status(thm)], [c_8691])).
% 9.07/3.33  tff(c_12542, plain, (![B_490]: (r2_hidden('#skF_1'('#skF_4', k3_subset_1('#skF_4', '#skF_5')), B_490) | ~r1_tarski('#skF_5', B_490))), inference(resolution, [status(thm)], [c_12447, c_4])).
% 9.07/3.33  tff(c_12633, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_4', '#skF_5')) | ~r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_12542, c_6])).
% 9.07/3.33  tff(c_12678, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_390, c_12633])).
% 9.07/3.33  tff(c_12680, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12448, c_12678])).
% 9.07/3.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.07/3.33  
% 9.07/3.33  Inference rules
% 9.07/3.33  ----------------------
% 9.07/3.33  #Ref     : 0
% 9.07/3.33  #Sup     : 2932
% 9.07/3.33  #Fact    : 12
% 9.07/3.33  #Define  : 0
% 9.07/3.33  #Split   : 11
% 9.07/3.33  #Chain   : 0
% 9.07/3.33  #Close   : 0
% 9.07/3.33  
% 9.07/3.33  Ordering : KBO
% 9.07/3.33  
% 9.07/3.33  Simplification rules
% 9.07/3.33  ----------------------
% 9.07/3.33  #Subsume      : 486
% 9.07/3.33  #Demod        : 2470
% 9.07/3.33  #Tautology    : 1020
% 9.07/3.33  #SimpNegUnit  : 98
% 9.07/3.33  #BackRed      : 78
% 9.07/3.33  
% 9.07/3.33  #Partial instantiations: 0
% 9.07/3.33  #Strategies tried      : 1
% 9.07/3.33  
% 9.07/3.33  Timing (in seconds)
% 9.07/3.33  ----------------------
% 9.07/3.33  Preprocessing        : 0.31
% 9.07/3.33  Parsing              : 0.16
% 9.07/3.33  CNF conversion       : 0.02
% 9.07/3.33  Main loop            : 2.22
% 9.07/3.33  Inferencing          : 0.58
% 9.07/3.33  Reduction            : 0.81
% 9.07/3.33  Demodulation         : 0.62
% 9.07/3.33  BG Simplification    : 0.07
% 9.07/3.33  Subsumption          : 0.59
% 9.07/3.33  Abstraction          : 0.09
% 9.07/3.33  MUC search           : 0.00
% 9.07/3.33  Cooper               : 0.00
% 9.07/3.33  Total                : 2.58
% 9.07/3.33  Index Insertion      : 0.00
% 9.07/3.34  Index Deletion       : 0.00
% 9.07/3.34  Index Matching       : 0.00
% 9.07/3.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
