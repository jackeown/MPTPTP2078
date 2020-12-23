%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:12 EST 2020

% Result     : Theorem 3.68s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 212 expanded)
%              Number of leaves         :   27 (  81 expanded)
%              Depth                    :   14
%              Number of atoms          :  114 ( 326 expanded)
%              Number of equality atoms :   52 ( 145 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_59,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_65,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_53,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1552,plain,(
    ! [A_129,B_130] :
      ( k4_xboole_0(A_129,B_130) = k3_subset_1(A_129,B_130)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(A_129)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1561,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_1552])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_186,plain,(
    ! [A_40,B_41] :
      ( k4_xboole_0(A_40,B_41) = k1_xboole_0
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_194,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_186])).

tff(c_30,plain,(
    ! [A_18] : k2_subset_1(A_18) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_34,plain,(
    ! [A_21] : m1_subset_1(k2_subset_1(A_21),k1_zfmisc_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_53,plain,(
    ! [A_21] : m1_subset_1(A_21,k1_zfmisc_1(A_21)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34])).

tff(c_671,plain,(
    ! [A_79,B_80] :
      ( k4_xboole_0(A_79,B_80) = k3_subset_1(A_79,B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_674,plain,(
    ! [A_21] : k4_xboole_0(A_21,A_21) = k3_subset_1(A_21,A_21) ),
    inference(resolution,[status(thm)],[c_53,c_671])).

tff(c_676,plain,(
    ! [A_21] : k3_subset_1(A_21,A_21) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_674])).

tff(c_24,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_380,plain,(
    ! [A_54,B_55,C_56] :
      ( r1_tarski(A_54,B_55)
      | ~ r1_tarski(A_54,k4_xboole_0(B_55,C_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_520,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(A_63,B_64)
      | ~ r1_tarski(A_63,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_380])).

tff(c_532,plain,(
    ! [A_5,B_64] :
      ( r1_tarski(A_5,B_64)
      | k4_xboole_0(A_5,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_520])).

tff(c_617,plain,(
    ! [A_74,B_75] :
      ( r1_tarski(A_74,B_75)
      | k1_xboole_0 != A_74 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_532])).

tff(c_46,plain,
    ( k2_subset_1('#skF_1') != '#skF_2'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_55,plain,
    ( '#skF_2' != '#skF_1'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_46])).

tff(c_103,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_55])).

tff(c_52,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | k2_subset_1('#skF_1') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_56,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_52])).

tff(c_238,plain,(
    '#skF_2' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_56])).

tff(c_239,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_238,c_103])).

tff(c_651,plain,(
    k3_subset_1('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_617,c_239])).

tff(c_683,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_676,c_651])).

tff(c_684,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_771,plain,(
    ! [A_84,B_85] :
      ( k4_xboole_0(A_84,B_85) = k1_xboole_0
      | ~ r1_tarski(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_783,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_771])).

tff(c_903,plain,(
    ! [A_95,B_96,C_97] :
      ( r1_tarski(A_95,B_96)
      | ~ r1_tarski(A_95,k4_xboole_0(B_96,C_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_972,plain,(
    ! [A_100,B_101] :
      ( r1_tarski(A_100,B_101)
      | ~ r1_tarski(A_100,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_783,c_903])).

tff(c_978,plain,(
    ! [A_5,B_101] :
      ( r1_tarski(A_5,B_101)
      | k4_xboole_0(A_5,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_972])).

tff(c_993,plain,(
    ! [B_101] : r1_tarski(k1_xboole_0,B_101) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_978])).

tff(c_1555,plain,(
    ! [A_21] : k4_xboole_0(A_21,A_21) = k3_subset_1(A_21,A_21) ),
    inference(resolution,[status(thm)],[c_53,c_1552])).

tff(c_1560,plain,(
    ! [A_21] : k3_subset_1(A_21,A_21) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_783,c_1555])).

tff(c_1728,plain,(
    ! [B_138,C_139,A_140] :
      ( r1_tarski(B_138,C_139)
      | ~ r1_tarski(k3_subset_1(A_140,C_139),k3_subset_1(A_140,B_138))
      | ~ m1_subset_1(C_139,k1_zfmisc_1(A_140))
      | ~ m1_subset_1(B_138,k1_zfmisc_1(A_140)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1737,plain,(
    ! [B_138,A_21] :
      ( r1_tarski(B_138,A_21)
      | ~ r1_tarski(k1_xboole_0,k3_subset_1(A_21,B_138))
      | ~ m1_subset_1(A_21,k1_zfmisc_1(A_21))
      | ~ m1_subset_1(B_138,k1_zfmisc_1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1560,c_1728])).

tff(c_2616,plain,(
    ! [B_172,A_173] :
      ( r1_tarski(B_172,A_173)
      | ~ m1_subset_1(B_172,k1_zfmisc_1(A_173)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_993,c_1737])).

tff(c_2625,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_2616])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2627,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_2625,c_4])).

tff(c_2633,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_684,c_2627])).

tff(c_2640,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_2633])).

tff(c_2643,plain,(
    k3_subset_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1561,c_2640])).

tff(c_685,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_781,plain,(
    k4_xboole_0(k3_subset_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_685,c_771])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2634,plain,(
    k4_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2625,c_12])).

tff(c_26,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2728,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) = k3_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2634,c_26])).

tff(c_2753,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_24,c_2728])).

tff(c_1593,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1561,c_26])).

tff(c_2768,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2753,c_1593])).

tff(c_835,plain,(
    ! [A_90,B_91] :
      ( k1_xboole_0 = A_90
      | ~ r1_tarski(A_90,k4_xboole_0(B_91,A_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_856,plain,(
    ! [A_5,B_91] :
      ( k1_xboole_0 = A_5
      | k4_xboole_0(A_5,k4_xboole_0(B_91,A_5)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_835])).

tff(c_3021,plain,
    ( k3_subset_1('#skF_1','#skF_2') = k1_xboole_0
    | k4_xboole_0(k3_subset_1('#skF_1','#skF_2'),'#skF_2') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2768,c_856])).

tff(c_3064,plain,(
    k3_subset_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_781,c_3021])).

tff(c_3066,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2643,c_3064])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.34  % CPULimit   : 60
% 0.20/0.34  % DateTime   : Tue Dec  1 13:05:36 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.68/1.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.68/1.79  
% 3.68/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.68/1.79  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.68/1.79  
% 3.68/1.79  %Foreground sorts:
% 3.68/1.79  
% 3.68/1.79  
% 3.68/1.79  %Background operators:
% 3.68/1.79  
% 3.68/1.79  
% 3.68/1.79  %Foreground operators:
% 3.68/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.68/1.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.68/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.68/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.68/1.79  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.68/1.79  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.68/1.79  tff('#skF_2', type, '#skF_2': $i).
% 3.68/1.79  tff('#skF_1', type, '#skF_1': $i).
% 3.68/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.68/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.68/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.68/1.79  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.68/1.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.68/1.79  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.68/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.68/1.79  
% 3.68/1.81  tff(f_87, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 3.68/1.81  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.68/1.81  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.68/1.81  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.68/1.81  tff(f_59, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.68/1.81  tff(f_65, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.68/1.81  tff(f_53, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.68/1.81  tff(f_43, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.68/1.81  tff(f_80, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 3.68/1.81  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.68/1.81  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.68/1.81  tff(f_51, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 3.68/1.81  tff(c_44, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.68/1.81  tff(c_1552, plain, (![A_129, B_130]: (k4_xboole_0(A_129, B_130)=k3_subset_1(A_129, B_130) | ~m1_subset_1(B_130, k1_zfmisc_1(A_129)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.68/1.81  tff(c_1561, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_1552])).
% 3.68/1.81  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.68/1.81  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.68/1.81  tff(c_186, plain, (![A_40, B_41]: (k4_xboole_0(A_40, B_41)=k1_xboole_0 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.68/1.81  tff(c_194, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_186])).
% 3.68/1.81  tff(c_30, plain, (![A_18]: (k2_subset_1(A_18)=A_18)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.68/1.81  tff(c_34, plain, (![A_21]: (m1_subset_1(k2_subset_1(A_21), k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.68/1.81  tff(c_53, plain, (![A_21]: (m1_subset_1(A_21, k1_zfmisc_1(A_21)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_34])).
% 3.68/1.81  tff(c_671, plain, (![A_79, B_80]: (k4_xboole_0(A_79, B_80)=k3_subset_1(A_79, B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(A_79)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.68/1.81  tff(c_674, plain, (![A_21]: (k4_xboole_0(A_21, A_21)=k3_subset_1(A_21, A_21))), inference(resolution, [status(thm)], [c_53, c_671])).
% 3.68/1.81  tff(c_676, plain, (![A_21]: (k3_subset_1(A_21, A_21)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_194, c_674])).
% 3.68/1.81  tff(c_24, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.68/1.81  tff(c_380, plain, (![A_54, B_55, C_56]: (r1_tarski(A_54, B_55) | ~r1_tarski(A_54, k4_xboole_0(B_55, C_56)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.68/1.81  tff(c_520, plain, (![A_63, B_64]: (r1_tarski(A_63, B_64) | ~r1_tarski(A_63, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_194, c_380])).
% 3.68/1.81  tff(c_532, plain, (![A_5, B_64]: (r1_tarski(A_5, B_64) | k4_xboole_0(A_5, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_520])).
% 3.68/1.81  tff(c_617, plain, (![A_74, B_75]: (r1_tarski(A_74, B_75) | k1_xboole_0!=A_74)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_532])).
% 3.68/1.81  tff(c_46, plain, (k2_subset_1('#skF_1')!='#skF_2' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.68/1.81  tff(c_55, plain, ('#skF_2'!='#skF_1' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_46])).
% 3.68/1.81  tff(c_103, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_55])).
% 3.68/1.81  tff(c_52, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | k2_subset_1('#skF_1')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.68/1.81  tff(c_56, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_52])).
% 3.68/1.81  tff(c_238, plain, ('#skF_2'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_103, c_56])).
% 3.68/1.81  tff(c_239, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_238, c_238, c_103])).
% 3.68/1.81  tff(c_651, plain, (k3_subset_1('#skF_1', '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_617, c_239])).
% 3.68/1.81  tff(c_683, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_676, c_651])).
% 3.68/1.81  tff(c_684, plain, ('#skF_2'!='#skF_1'), inference(splitRight, [status(thm)], [c_55])).
% 3.68/1.81  tff(c_771, plain, (![A_84, B_85]: (k4_xboole_0(A_84, B_85)=k1_xboole_0 | ~r1_tarski(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.68/1.81  tff(c_783, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_771])).
% 3.68/1.81  tff(c_903, plain, (![A_95, B_96, C_97]: (r1_tarski(A_95, B_96) | ~r1_tarski(A_95, k4_xboole_0(B_96, C_97)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.68/1.81  tff(c_972, plain, (![A_100, B_101]: (r1_tarski(A_100, B_101) | ~r1_tarski(A_100, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_783, c_903])).
% 3.68/1.81  tff(c_978, plain, (![A_5, B_101]: (r1_tarski(A_5, B_101) | k4_xboole_0(A_5, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_972])).
% 3.68/1.81  tff(c_993, plain, (![B_101]: (r1_tarski(k1_xboole_0, B_101))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_978])).
% 3.68/1.81  tff(c_1555, plain, (![A_21]: (k4_xboole_0(A_21, A_21)=k3_subset_1(A_21, A_21))), inference(resolution, [status(thm)], [c_53, c_1552])).
% 3.68/1.81  tff(c_1560, plain, (![A_21]: (k3_subset_1(A_21, A_21)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_783, c_1555])).
% 3.68/1.81  tff(c_1728, plain, (![B_138, C_139, A_140]: (r1_tarski(B_138, C_139) | ~r1_tarski(k3_subset_1(A_140, C_139), k3_subset_1(A_140, B_138)) | ~m1_subset_1(C_139, k1_zfmisc_1(A_140)) | ~m1_subset_1(B_138, k1_zfmisc_1(A_140)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.68/1.81  tff(c_1737, plain, (![B_138, A_21]: (r1_tarski(B_138, A_21) | ~r1_tarski(k1_xboole_0, k3_subset_1(A_21, B_138)) | ~m1_subset_1(A_21, k1_zfmisc_1(A_21)) | ~m1_subset_1(B_138, k1_zfmisc_1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_1560, c_1728])).
% 3.68/1.81  tff(c_2616, plain, (![B_172, A_173]: (r1_tarski(B_172, A_173) | ~m1_subset_1(B_172, k1_zfmisc_1(A_173)))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_993, c_1737])).
% 3.68/1.81  tff(c_2625, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_44, c_2616])).
% 3.68/1.81  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.68/1.81  tff(c_2627, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_2625, c_4])).
% 3.68/1.81  tff(c_2633, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_684, c_2627])).
% 3.68/1.81  tff(c_2640, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_2633])).
% 3.68/1.81  tff(c_2643, plain, (k3_subset_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1561, c_2640])).
% 3.68/1.81  tff(c_685, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_55])).
% 3.68/1.81  tff(c_781, plain, (k4_xboole_0(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_685, c_771])).
% 3.68/1.81  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.68/1.81  tff(c_12, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.68/1.81  tff(c_2634, plain, (k4_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_2625, c_12])).
% 3.68/1.81  tff(c_26, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.68/1.81  tff(c_2728, plain, (k4_xboole_0('#skF_2', k1_xboole_0)=k3_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2634, c_26])).
% 3.68/1.81  tff(c_2753, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_24, c_2728])).
% 3.68/1.81  tff(c_1593, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1561, c_26])).
% 3.68/1.81  tff(c_2768, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2753, c_1593])).
% 3.68/1.81  tff(c_835, plain, (![A_90, B_91]: (k1_xboole_0=A_90 | ~r1_tarski(A_90, k4_xboole_0(B_91, A_90)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.68/1.81  tff(c_856, plain, (![A_5, B_91]: (k1_xboole_0=A_5 | k4_xboole_0(A_5, k4_xboole_0(B_91, A_5))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_835])).
% 3.68/1.81  tff(c_3021, plain, (k3_subset_1('#skF_1', '#skF_2')=k1_xboole_0 | k4_xboole_0(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2768, c_856])).
% 3.68/1.81  tff(c_3064, plain, (k3_subset_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_781, c_3021])).
% 3.68/1.81  tff(c_3066, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2643, c_3064])).
% 3.68/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.68/1.81  
% 3.68/1.81  Inference rules
% 3.68/1.81  ----------------------
% 3.68/1.81  #Ref     : 1
% 3.68/1.81  #Sup     : 728
% 3.68/1.81  #Fact    : 0
% 3.68/1.81  #Define  : 0
% 3.68/1.81  #Split   : 4
% 3.68/1.81  #Chain   : 0
% 3.68/1.81  #Close   : 0
% 3.68/1.81  
% 3.68/1.81  Ordering : KBO
% 3.68/1.81  
% 3.68/1.81  Simplification rules
% 3.68/1.81  ----------------------
% 3.68/1.81  #Subsume      : 91
% 3.68/1.81  #Demod        : 362
% 3.68/1.81  #Tautology    : 421
% 3.68/1.81  #SimpNegUnit  : 17
% 3.68/1.81  #BackRed      : 8
% 3.68/1.81  
% 3.68/1.81  #Partial instantiations: 0
% 3.68/1.81  #Strategies tried      : 1
% 3.68/1.81  
% 3.68/1.81  Timing (in seconds)
% 3.68/1.81  ----------------------
% 3.85/1.81  Preprocessing        : 0.35
% 3.85/1.81  Parsing              : 0.19
% 3.85/1.81  CNF conversion       : 0.02
% 3.85/1.81  Main loop            : 0.58
% 3.85/1.81  Inferencing          : 0.19
% 3.85/1.81  Reduction            : 0.22
% 3.85/1.81  Demodulation         : 0.17
% 3.85/1.81  BG Simplification    : 0.02
% 3.85/1.81  Subsumption          : 0.10
% 3.85/1.81  Abstraction          : 0.03
% 3.85/1.81  MUC search           : 0.00
% 3.85/1.81  Cooper               : 0.00
% 3.85/1.81  Total                : 0.96
% 3.85/1.81  Index Insertion      : 0.00
% 3.85/1.81  Index Deletion       : 0.00
% 3.85/1.81  Index Matching       : 0.00
% 3.85/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
