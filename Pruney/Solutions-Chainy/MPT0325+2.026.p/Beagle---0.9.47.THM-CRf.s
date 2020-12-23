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
% DateTime   : Thu Dec  3 09:54:24 EST 2020

% Result     : Theorem 10.75s
% Output     : CNFRefutation 10.85s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 300 expanded)
%              Number of leaves         :   27 ( 110 expanded)
%              Depth                    :   20
%              Number of atoms          :  209 ( 570 expanded)
%              Number of equality atoms :   92 ( 225 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_51,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_82,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_63,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
          | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
        & ~ r1_tarski(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

tff(c_121,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | k4_xboole_0(A_38,B_39) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_56,plain,
    ( ~ r1_tarski('#skF_5','#skF_7')
    | ~ r1_tarski('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_94,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_129,plain,(
    k4_xboole_0('#skF_4','#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_121,c_94])).

tff(c_173,plain,(
    ! [A_51,B_52] :
      ( r2_hidden('#skF_1'(A_51,B_52),A_51)
      | r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_24957,plain,(
    ! [A_595,B_596,B_597] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_595,B_596),B_597),A_595)
      | r1_tarski(k3_xboole_0(A_595,B_596),B_597) ) ),
    inference(resolution,[status(thm)],[c_173,c_12])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_25053,plain,(
    ! [A_598,B_599] : r1_tarski(k3_xboole_0(A_598,B_599),A_598) ),
    inference(resolution,[status(thm)],[c_24957,c_4])).

tff(c_34,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = k1_xboole_0
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_25145,plain,(
    ! [A_598,B_599] : k4_xboole_0(k3_xboole_0(A_598,B_599),A_598) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_25053,c_34])).

tff(c_30,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_410,plain,(
    ! [C_76,A_77,B_78] :
      ( r1_tarski(k2_zfmisc_1(C_76,A_77),k2_zfmisc_1(C_76,B_78))
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_433,plain,(
    ! [C_76,A_77,B_78] :
      ( k4_xboole_0(k2_zfmisc_1(C_76,A_77),k2_zfmisc_1(C_76,B_78)) = k1_xboole_0
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(resolution,[status(thm)],[c_410,c_34])).

tff(c_25037,plain,(
    ! [A_595,B_596] : r1_tarski(k3_xboole_0(A_595,B_596),A_595) ),
    inference(resolution,[status(thm)],[c_24957,c_4])).

tff(c_256,plain,(
    ! [A_65,C_66,B_67] :
      ( r1_tarski(k2_zfmisc_1(A_65,C_66),k2_zfmisc_1(B_67,C_66))
      | ~ r1_tarski(A_65,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_279,plain,(
    ! [A_65,C_66,B_67] :
      ( k4_xboole_0(k2_zfmisc_1(A_65,C_66),k2_zfmisc_1(B_67,C_66)) = k1_xboole_0
      | ~ r1_tarski(A_65,B_67) ) ),
    inference(resolution,[status(thm)],[c_256,c_34])).

tff(c_58,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2147,plain,(
    ! [A_144,C_145,B_146,D_147] : k3_xboole_0(k2_zfmisc_1(A_144,C_145),k2_zfmisc_1(B_146,D_147)) = k2_zfmisc_1(k3_xboole_0(A_144,B_146),k3_xboole_0(C_145,D_147)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_60,plain,(
    r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_130,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = A_40
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_141,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_6','#skF_7')) = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_130])).

tff(c_2156,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_4','#skF_6'),k3_xboole_0('#skF_5','#skF_7')) = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2147,c_141])).

tff(c_38,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_32,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | k4_xboole_0(A_14,B_15) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_44,plain,(
    ! [B_20] : k2_zfmisc_1(k1_xboole_0,B_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_303,plain,(
    ! [A_70,B_71] :
      ( r1_tarski(k2_zfmisc_1(A_70,B_71),k1_xboole_0)
      | ~ r1_tarski(A_70,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_256])).

tff(c_311,plain,(
    ! [A_70,B_71] :
      ( k4_xboole_0(k2_zfmisc_1(A_70,B_71),k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(A_70,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_303,c_34])).

tff(c_325,plain,(
    ! [A_72,B_73] :
      ( k2_zfmisc_1(A_72,B_73) = k1_xboole_0
      | ~ r1_tarski(A_72,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_311])).

tff(c_330,plain,(
    ! [A_14,B_73] :
      ( k2_zfmisc_1(A_14,B_73) = k1_xboole_0
      | k4_xboole_0(A_14,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_325])).

tff(c_336,plain,(
    ! [A_14,B_73] :
      ( k2_zfmisc_1(A_14,B_73) = k1_xboole_0
      | k1_xboole_0 != A_14 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_330])).

tff(c_2310,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0
    | k3_xboole_0('#skF_4','#skF_6') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2156,c_336])).

tff(c_2337,plain,(
    k3_xboole_0('#skF_4','#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2310])).

tff(c_1368,plain,(
    ! [A_121,B_122,C_123] :
      ( ~ r1_tarski(k2_zfmisc_1(A_121,B_122),k2_zfmisc_1(A_121,C_123))
      | r1_tarski(B_122,C_123)
      | k1_xboole_0 = A_121 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_26665,plain,(
    ! [B_624,C_625,A_626] :
      ( r1_tarski(B_624,C_625)
      | k1_xboole_0 = A_626
      | k4_xboole_0(k2_zfmisc_1(A_626,B_624),k2_zfmisc_1(A_626,C_625)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_1368])).

tff(c_26690,plain,(
    ! [B_624] :
      ( r1_tarski(B_624,k3_xboole_0('#skF_5','#skF_7'))
      | k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0
      | k4_xboole_0(k2_zfmisc_1(k3_xboole_0('#skF_4','#skF_6'),B_624),k2_zfmisc_1('#skF_4','#skF_5')) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2156,c_26665])).

tff(c_26784,plain,(
    ! [B_627] :
      ( r1_tarski(B_627,k3_xboole_0('#skF_5','#skF_7'))
      | k4_xboole_0(k2_zfmisc_1(k3_xboole_0('#skF_4','#skF_6'),B_627),k2_zfmisc_1('#skF_4','#skF_5')) != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_2337,c_26690])).

tff(c_26788,plain,
    ( r1_tarski('#skF_5',k3_xboole_0('#skF_5','#skF_7'))
    | ~ r1_tarski(k3_xboole_0('#skF_4','#skF_6'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_26784])).

tff(c_26824,plain,(
    r1_tarski('#skF_5',k3_xboole_0('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25037,c_26788])).

tff(c_156,plain,(
    ! [B_46,A_47] :
      ( B_46 = A_47
      | ~ r1_tarski(B_46,A_47)
      | ~ r1_tarski(A_47,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_163,plain,(
    ! [B_15,A_14] :
      ( B_15 = A_14
      | ~ r1_tarski(B_15,A_14)
      | k4_xboole_0(A_14,B_15) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_156])).

tff(c_26851,plain,
    ( k3_xboole_0('#skF_5','#skF_7') = '#skF_5'
    | k4_xboole_0(k3_xboole_0('#skF_5','#skF_7'),'#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26824,c_163])).

tff(c_26866,plain,(
    k3_xboole_0('#skF_5','#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25145,c_26851])).

tff(c_42,plain,(
    ! [A_19] : k2_zfmisc_1(A_19,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_455,plain,(
    ! [A_81,A_82] :
      ( r1_tarski(k2_zfmisc_1(A_81,A_82),k1_xboole_0)
      | ~ r1_tarski(A_82,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_410])).

tff(c_465,plain,(
    ! [A_81,A_82] :
      ( k4_xboole_0(k2_zfmisc_1(A_81,A_82),k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(A_82,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_455,c_34])).

tff(c_480,plain,(
    ! [A_83,A_84] :
      ( k2_zfmisc_1(A_83,A_84) = k1_xboole_0
      | ~ r1_tarski(A_84,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_465])).

tff(c_487,plain,(
    ! [A_83,A_14] :
      ( k2_zfmisc_1(A_83,A_14) = k1_xboole_0
      | k4_xboole_0(A_14,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_480])).

tff(c_494,plain,(
    ! [A_83,A_14] :
      ( k2_zfmisc_1(A_83,A_14) = k1_xboole_0
      | k1_xboole_0 != A_14 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_487])).

tff(c_2295,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0
    | k3_xboole_0('#skF_5','#skF_7') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2156,c_494])).

tff(c_2336,plain,(
    k3_xboole_0('#skF_5','#skF_7') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2295])).

tff(c_784,plain,(
    ! [B_100,A_101,C_102] :
      ( ~ r1_tarski(k2_zfmisc_1(B_100,A_101),k2_zfmisc_1(C_102,A_101))
      | r1_tarski(B_100,C_102)
      | k1_xboole_0 = A_101 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_26446,plain,(
    ! [B_618,C_619,A_620] :
      ( r1_tarski(B_618,C_619)
      | k1_xboole_0 = A_620
      | k4_xboole_0(k2_zfmisc_1(B_618,A_620),k2_zfmisc_1(C_619,A_620)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_784])).

tff(c_26471,plain,(
    ! [B_618] :
      ( r1_tarski(B_618,k3_xboole_0('#skF_4','#skF_6'))
      | k3_xboole_0('#skF_5','#skF_7') = k1_xboole_0
      | k4_xboole_0(k2_zfmisc_1(B_618,k3_xboole_0('#skF_5','#skF_7')),k2_zfmisc_1('#skF_4','#skF_5')) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2156,c_26446])).

tff(c_26535,plain,(
    ! [B_618] :
      ( r1_tarski(B_618,k3_xboole_0('#skF_4','#skF_6'))
      | k4_xboole_0(k2_zfmisc_1(B_618,k3_xboole_0('#skF_5','#skF_7')),k2_zfmisc_1('#skF_4','#skF_5')) != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_2336,c_26471])).

tff(c_27543,plain,(
    ! [B_638] :
      ( r1_tarski(B_638,k3_xboole_0('#skF_4','#skF_6'))
      | k4_xboole_0(k2_zfmisc_1(B_638,'#skF_5'),k2_zfmisc_1('#skF_4','#skF_5')) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26866,c_26535])).

tff(c_27559,plain,
    ( r1_tarski('#skF_4',k3_xboole_0('#skF_4','#skF_6'))
    | ~ r1_tarski('#skF_5','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_433,c_27543])).

tff(c_27595,plain,(
    r1_tarski('#skF_4',k3_xboole_0('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_27559])).

tff(c_27619,plain,
    ( k3_xboole_0('#skF_4','#skF_6') = '#skF_4'
    | k4_xboole_0(k3_xboole_0('#skF_4','#skF_6'),'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_27595,c_163])).

tff(c_27634,plain,(
    k3_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25145,c_27619])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26044,plain,(
    ! [A_607,B_608,B_609] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_607,B_608),B_609),B_608)
      | r1_tarski(k3_xboole_0(A_607,B_608),B_609) ) ),
    inference(resolution,[status(thm)],[c_173,c_10])).

tff(c_26095,plain,(
    ! [A_610,B_611] : r1_tarski(k3_xboole_0(A_610,B_611),B_611) ),
    inference(resolution,[status(thm)],[c_26044,c_4])).

tff(c_26151,plain,(
    ! [A_610,B_611] : k4_xboole_0(k3_xboole_0(A_610,B_611),B_611) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26095,c_34])).

tff(c_27655,plain,(
    k4_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_27634,c_26151])).

tff(c_27683,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_27655])).

tff(c_27684,plain,(
    ~ r1_tarski('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,(
    ! [A_24,C_26,B_25] :
      ( r1_tarski(k2_zfmisc_1(A_24,C_26),k2_zfmisc_1(B_25,C_26))
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_27937,plain,(
    ! [A_675,C_676,B_677] :
      ( r1_tarski(k2_zfmisc_1(A_675,C_676),k2_zfmisc_1(B_677,C_676))
      | ~ r1_tarski(A_675,B_677) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_28198,plain,(
    ! [A_694,B_695] :
      ( r1_tarski(k2_zfmisc_1(A_694,B_695),k1_xboole_0)
      | ~ r1_tarski(A_694,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_27937])).

tff(c_28211,plain,(
    ! [A_694,B_695] :
      ( k4_xboole_0(k2_zfmisc_1(A_694,B_695),k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(A_694,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_28198,c_34])).

tff(c_28228,plain,(
    ! [A_696,B_697] :
      ( k2_zfmisc_1(A_696,B_697) = k1_xboole_0
      | ~ r1_tarski(A_696,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_28211])).

tff(c_28235,plain,(
    ! [A_14,B_697] :
      ( k2_zfmisc_1(A_14,B_697) = k1_xboole_0
      | k4_xboole_0(A_14,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_28228])).

tff(c_28247,plain,(
    ! [A_698,B_699] :
      ( k2_zfmisc_1(A_698,B_699) = k1_xboole_0
      | k1_xboole_0 != A_698 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_28235])).

tff(c_28323,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_28247,c_58])).

tff(c_27685,plain,(
    r1_tarski('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_27695,plain,(
    ! [A_641,B_642] :
      ( k3_xboole_0(A_641,B_642) = A_641
      | ~ r1_tarski(A_641,B_642) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_27702,plain,(
    k3_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_27685,c_27695])).

tff(c_29098,plain,(
    ! [A_732,C_733,B_734,D_735] : k3_xboole_0(k2_zfmisc_1(A_732,C_733),k2_zfmisc_1(B_734,D_735)) = k2_zfmisc_1(k3_xboole_0(A_732,B_734),k3_xboole_0(C_733,D_735)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_36,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_27735,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_6','#skF_7')) = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_36])).

tff(c_29107,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_4','#skF_6'),k3_xboole_0('#skF_5','#skF_7')) = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_29098,c_27735])).

tff(c_29165,plain,(
    k2_zfmisc_1('#skF_4',k3_xboole_0('#skF_5','#skF_7')) = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27702,c_29107])).

tff(c_46,plain,(
    ! [A_21,B_22,C_23] :
      ( ~ r1_tarski(k2_zfmisc_1(A_21,B_22),k2_zfmisc_1(A_21,C_23))
      | r1_tarski(B_22,C_23)
      | k1_xboole_0 = A_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_29289,plain,(
    ! [B_22] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4',B_22),k2_zfmisc_1('#skF_4','#skF_5'))
      | r1_tarski(B_22,k3_xboole_0('#skF_5','#skF_7'))
      | k1_xboole_0 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29165,c_46])).

tff(c_33207,plain,(
    ! [B_843] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4',B_843),k2_zfmisc_1('#skF_4','#skF_5'))
      | r1_tarski(B_843,k3_xboole_0('#skF_5','#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28323,c_29289])).

tff(c_33248,plain,
    ( r1_tarski('#skF_5',k3_xboole_0('#skF_5','#skF_7'))
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_33207])).

tff(c_33261,plain,(
    r1_tarski('#skF_5',k3_xboole_0('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_33248])).

tff(c_33290,plain,(
    k4_xboole_0('#skF_5',k3_xboole_0('#skF_5','#skF_7')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_33261,c_34])).

tff(c_29286,plain,(
    ! [C_23] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_4',C_23))
      | r1_tarski(k3_xboole_0('#skF_5','#skF_7'),C_23)
      | k1_xboole_0 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29165,c_46])).

tff(c_33497,plain,(
    ! [C_849] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_4',C_849))
      | r1_tarski(k3_xboole_0('#skF_5','#skF_7'),C_849) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28323,c_29286])).

tff(c_33538,plain,
    ( r1_tarski(k3_xboole_0('#skF_5','#skF_7'),'#skF_5')
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_33497])).

tff(c_33551,plain,(
    r1_tarski(k3_xboole_0('#skF_5','#skF_7'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_33538])).

tff(c_27771,plain,(
    ! [B_651,A_652] :
      ( B_651 = A_652
      | ~ r1_tarski(B_651,A_652)
      | ~ r1_tarski(A_652,B_651) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_27780,plain,(
    ! [B_15,A_14] :
      ( B_15 = A_14
      | ~ r1_tarski(B_15,A_14)
      | k4_xboole_0(A_14,B_15) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_27771])).

tff(c_33564,plain,
    ( k3_xboole_0('#skF_5','#skF_7') = '#skF_5'
    | k4_xboole_0('#skF_5',k3_xboole_0('#skF_5','#skF_7')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_33551,c_27780])).

tff(c_33579,plain,(
    k3_xboole_0('#skF_5','#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33290,c_33564])).

tff(c_33742,plain,(
    ! [D_853] :
      ( r2_hidden(D_853,'#skF_7')
      | ~ r2_hidden(D_853,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33579,c_10])).

tff(c_33773,plain,(
    ! [A_854] :
      ( r1_tarski(A_854,'#skF_7')
      | ~ r2_hidden('#skF_1'(A_854,'#skF_7'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_33742,c_4])).

tff(c_33777,plain,(
    r1_tarski('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_6,c_33773])).

tff(c_33781,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27684,c_27684,c_33777])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:16:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.75/4.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.75/4.12  
% 10.75/4.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.75/4.12  %$ r2_hidden > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 10.75/4.12  
% 10.75/4.12  %Foreground sorts:
% 10.75/4.12  
% 10.75/4.12  
% 10.75/4.12  %Background operators:
% 10.75/4.12  
% 10.75/4.12  
% 10.75/4.12  %Foreground operators:
% 10.75/4.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.75/4.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.75/4.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.75/4.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.75/4.12  tff('#skF_7', type, '#skF_7': $i).
% 10.75/4.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.75/4.12  tff('#skF_5', type, '#skF_5': $i).
% 10.75/4.12  tff('#skF_6', type, '#skF_6': $i).
% 10.75/4.12  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.75/4.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.75/4.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.75/4.12  tff('#skF_4', type, '#skF_4': $i).
% 10.75/4.12  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 10.75/4.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.75/4.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.75/4.12  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.75/4.12  
% 10.85/4.14  tff(f_51, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 10.85/4.14  tff(f_91, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 10.85/4.14  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 10.85/4.14  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 10.85/4.14  tff(f_47, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.85/4.14  tff(f_80, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 10.85/4.14  tff(f_82, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 10.85/4.14  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 10.85/4.14  tff(f_57, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 10.85/4.14  tff(f_63, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 10.85/4.14  tff(f_74, axiom, (![A, B, C]: ~((~(A = k1_xboole_0) & (r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(C, A)) | r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(A, C)))) & ~r1_tarski(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 10.85/4.14  tff(c_121, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | k4_xboole_0(A_38, B_39)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.85/4.14  tff(c_56, plain, (~r1_tarski('#skF_5', '#skF_7') | ~r1_tarski('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.85/4.14  tff(c_94, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_56])).
% 10.85/4.14  tff(c_129, plain, (k4_xboole_0('#skF_4', '#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_121, c_94])).
% 10.85/4.14  tff(c_173, plain, (![A_51, B_52]: (r2_hidden('#skF_1'(A_51, B_52), A_51) | r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.85/4.14  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.85/4.14  tff(c_24957, plain, (![A_595, B_596, B_597]: (r2_hidden('#skF_1'(k3_xboole_0(A_595, B_596), B_597), A_595) | r1_tarski(k3_xboole_0(A_595, B_596), B_597))), inference(resolution, [status(thm)], [c_173, c_12])).
% 10.85/4.14  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.85/4.14  tff(c_25053, plain, (![A_598, B_599]: (r1_tarski(k3_xboole_0(A_598, B_599), A_598))), inference(resolution, [status(thm)], [c_24957, c_4])).
% 10.85/4.14  tff(c_34, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=k1_xboole_0 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.85/4.14  tff(c_25145, plain, (![A_598, B_599]: (k4_xboole_0(k3_xboole_0(A_598, B_599), A_598)=k1_xboole_0)), inference(resolution, [status(thm)], [c_25053, c_34])).
% 10.85/4.14  tff(c_30, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.85/4.14  tff(c_410, plain, (![C_76, A_77, B_78]: (r1_tarski(k2_zfmisc_1(C_76, A_77), k2_zfmisc_1(C_76, B_78)) | ~r1_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.85/4.14  tff(c_433, plain, (![C_76, A_77, B_78]: (k4_xboole_0(k2_zfmisc_1(C_76, A_77), k2_zfmisc_1(C_76, B_78))=k1_xboole_0 | ~r1_tarski(A_77, B_78))), inference(resolution, [status(thm)], [c_410, c_34])).
% 10.85/4.14  tff(c_25037, plain, (![A_595, B_596]: (r1_tarski(k3_xboole_0(A_595, B_596), A_595))), inference(resolution, [status(thm)], [c_24957, c_4])).
% 10.85/4.14  tff(c_256, plain, (![A_65, C_66, B_67]: (r1_tarski(k2_zfmisc_1(A_65, C_66), k2_zfmisc_1(B_67, C_66)) | ~r1_tarski(A_65, B_67))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.85/4.14  tff(c_279, plain, (![A_65, C_66, B_67]: (k4_xboole_0(k2_zfmisc_1(A_65, C_66), k2_zfmisc_1(B_67, C_66))=k1_xboole_0 | ~r1_tarski(A_65, B_67))), inference(resolution, [status(thm)], [c_256, c_34])).
% 10.85/4.14  tff(c_58, plain, (k2_zfmisc_1('#skF_4', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.85/4.14  tff(c_2147, plain, (![A_144, C_145, B_146, D_147]: (k3_xboole_0(k2_zfmisc_1(A_144, C_145), k2_zfmisc_1(B_146, D_147))=k2_zfmisc_1(k3_xboole_0(A_144, B_146), k3_xboole_0(C_145, D_147)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.85/4.14  tff(c_60, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.85/4.14  tff(c_130, plain, (![A_40, B_41]: (k3_xboole_0(A_40, B_41)=A_40 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.85/4.14  tff(c_141, plain, (k3_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_6', '#skF_7'))=k2_zfmisc_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_60, c_130])).
% 10.85/4.14  tff(c_2156, plain, (k2_zfmisc_1(k3_xboole_0('#skF_4', '#skF_6'), k3_xboole_0('#skF_5', '#skF_7'))=k2_zfmisc_1('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2147, c_141])).
% 10.85/4.14  tff(c_38, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.85/4.14  tff(c_32, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | k4_xboole_0(A_14, B_15)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.85/4.14  tff(c_44, plain, (![B_20]: (k2_zfmisc_1(k1_xboole_0, B_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.85/4.14  tff(c_303, plain, (![A_70, B_71]: (r1_tarski(k2_zfmisc_1(A_70, B_71), k1_xboole_0) | ~r1_tarski(A_70, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_44, c_256])).
% 10.85/4.14  tff(c_311, plain, (![A_70, B_71]: (k4_xboole_0(k2_zfmisc_1(A_70, B_71), k1_xboole_0)=k1_xboole_0 | ~r1_tarski(A_70, k1_xboole_0))), inference(resolution, [status(thm)], [c_303, c_34])).
% 10.85/4.14  tff(c_325, plain, (![A_72, B_73]: (k2_zfmisc_1(A_72, B_73)=k1_xboole_0 | ~r1_tarski(A_72, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_311])).
% 10.85/4.14  tff(c_330, plain, (![A_14, B_73]: (k2_zfmisc_1(A_14, B_73)=k1_xboole_0 | k4_xboole_0(A_14, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_325])).
% 10.85/4.14  tff(c_336, plain, (![A_14, B_73]: (k2_zfmisc_1(A_14, B_73)=k1_xboole_0 | k1_xboole_0!=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_330])).
% 10.85/4.14  tff(c_2310, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0 | k3_xboole_0('#skF_4', '#skF_6')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2156, c_336])).
% 10.85/4.14  tff(c_2337, plain, (k3_xboole_0('#skF_4', '#skF_6')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_58, c_2310])).
% 10.85/4.14  tff(c_1368, plain, (![A_121, B_122, C_123]: (~r1_tarski(k2_zfmisc_1(A_121, B_122), k2_zfmisc_1(A_121, C_123)) | r1_tarski(B_122, C_123) | k1_xboole_0=A_121)), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.85/4.14  tff(c_26665, plain, (![B_624, C_625, A_626]: (r1_tarski(B_624, C_625) | k1_xboole_0=A_626 | k4_xboole_0(k2_zfmisc_1(A_626, B_624), k2_zfmisc_1(A_626, C_625))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_1368])).
% 10.85/4.14  tff(c_26690, plain, (![B_624]: (r1_tarski(B_624, k3_xboole_0('#skF_5', '#skF_7')) | k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0 | k4_xboole_0(k2_zfmisc_1(k3_xboole_0('#skF_4', '#skF_6'), B_624), k2_zfmisc_1('#skF_4', '#skF_5'))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2156, c_26665])).
% 10.85/4.14  tff(c_26784, plain, (![B_627]: (r1_tarski(B_627, k3_xboole_0('#skF_5', '#skF_7')) | k4_xboole_0(k2_zfmisc_1(k3_xboole_0('#skF_4', '#skF_6'), B_627), k2_zfmisc_1('#skF_4', '#skF_5'))!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_2337, c_26690])).
% 10.85/4.14  tff(c_26788, plain, (r1_tarski('#skF_5', k3_xboole_0('#skF_5', '#skF_7')) | ~r1_tarski(k3_xboole_0('#skF_4', '#skF_6'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_279, c_26784])).
% 10.85/4.14  tff(c_26824, plain, (r1_tarski('#skF_5', k3_xboole_0('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_25037, c_26788])).
% 10.85/4.14  tff(c_156, plain, (![B_46, A_47]: (B_46=A_47 | ~r1_tarski(B_46, A_47) | ~r1_tarski(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.85/4.14  tff(c_163, plain, (![B_15, A_14]: (B_15=A_14 | ~r1_tarski(B_15, A_14) | k4_xboole_0(A_14, B_15)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_156])).
% 10.85/4.14  tff(c_26851, plain, (k3_xboole_0('#skF_5', '#skF_7')='#skF_5' | k4_xboole_0(k3_xboole_0('#skF_5', '#skF_7'), '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_26824, c_163])).
% 10.85/4.14  tff(c_26866, plain, (k3_xboole_0('#skF_5', '#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_25145, c_26851])).
% 10.85/4.14  tff(c_42, plain, (![A_19]: (k2_zfmisc_1(A_19, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.85/4.14  tff(c_455, plain, (![A_81, A_82]: (r1_tarski(k2_zfmisc_1(A_81, A_82), k1_xboole_0) | ~r1_tarski(A_82, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_42, c_410])).
% 10.85/4.14  tff(c_465, plain, (![A_81, A_82]: (k4_xboole_0(k2_zfmisc_1(A_81, A_82), k1_xboole_0)=k1_xboole_0 | ~r1_tarski(A_82, k1_xboole_0))), inference(resolution, [status(thm)], [c_455, c_34])).
% 10.85/4.14  tff(c_480, plain, (![A_83, A_84]: (k2_zfmisc_1(A_83, A_84)=k1_xboole_0 | ~r1_tarski(A_84, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_465])).
% 10.85/4.14  tff(c_487, plain, (![A_83, A_14]: (k2_zfmisc_1(A_83, A_14)=k1_xboole_0 | k4_xboole_0(A_14, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_480])).
% 10.85/4.14  tff(c_494, plain, (![A_83, A_14]: (k2_zfmisc_1(A_83, A_14)=k1_xboole_0 | k1_xboole_0!=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_487])).
% 10.85/4.14  tff(c_2295, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0 | k3_xboole_0('#skF_5', '#skF_7')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2156, c_494])).
% 10.85/4.14  tff(c_2336, plain, (k3_xboole_0('#skF_5', '#skF_7')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_58, c_2295])).
% 10.85/4.14  tff(c_784, plain, (![B_100, A_101, C_102]: (~r1_tarski(k2_zfmisc_1(B_100, A_101), k2_zfmisc_1(C_102, A_101)) | r1_tarski(B_100, C_102) | k1_xboole_0=A_101)), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.85/4.14  tff(c_26446, plain, (![B_618, C_619, A_620]: (r1_tarski(B_618, C_619) | k1_xboole_0=A_620 | k4_xboole_0(k2_zfmisc_1(B_618, A_620), k2_zfmisc_1(C_619, A_620))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_784])).
% 10.85/4.14  tff(c_26471, plain, (![B_618]: (r1_tarski(B_618, k3_xboole_0('#skF_4', '#skF_6')) | k3_xboole_0('#skF_5', '#skF_7')=k1_xboole_0 | k4_xboole_0(k2_zfmisc_1(B_618, k3_xboole_0('#skF_5', '#skF_7')), k2_zfmisc_1('#skF_4', '#skF_5'))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2156, c_26446])).
% 10.85/4.14  tff(c_26535, plain, (![B_618]: (r1_tarski(B_618, k3_xboole_0('#skF_4', '#skF_6')) | k4_xboole_0(k2_zfmisc_1(B_618, k3_xboole_0('#skF_5', '#skF_7')), k2_zfmisc_1('#skF_4', '#skF_5'))!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_2336, c_26471])).
% 10.85/4.14  tff(c_27543, plain, (![B_638]: (r1_tarski(B_638, k3_xboole_0('#skF_4', '#skF_6')) | k4_xboole_0(k2_zfmisc_1(B_638, '#skF_5'), k2_zfmisc_1('#skF_4', '#skF_5'))!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26866, c_26535])).
% 10.85/4.14  tff(c_27559, plain, (r1_tarski('#skF_4', k3_xboole_0('#skF_4', '#skF_6')) | ~r1_tarski('#skF_5', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_433, c_27543])).
% 10.85/4.14  tff(c_27595, plain, (r1_tarski('#skF_4', k3_xboole_0('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_27559])).
% 10.85/4.14  tff(c_27619, plain, (k3_xboole_0('#skF_4', '#skF_6')='#skF_4' | k4_xboole_0(k3_xboole_0('#skF_4', '#skF_6'), '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_27595, c_163])).
% 10.85/4.14  tff(c_27634, plain, (k3_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_25145, c_27619])).
% 10.85/4.14  tff(c_10, plain, (![D_11, B_7, A_6]: (r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.85/4.14  tff(c_26044, plain, (![A_607, B_608, B_609]: (r2_hidden('#skF_1'(k3_xboole_0(A_607, B_608), B_609), B_608) | r1_tarski(k3_xboole_0(A_607, B_608), B_609))), inference(resolution, [status(thm)], [c_173, c_10])).
% 10.85/4.14  tff(c_26095, plain, (![A_610, B_611]: (r1_tarski(k3_xboole_0(A_610, B_611), B_611))), inference(resolution, [status(thm)], [c_26044, c_4])).
% 10.85/4.14  tff(c_26151, plain, (![A_610, B_611]: (k4_xboole_0(k3_xboole_0(A_610, B_611), B_611)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26095, c_34])).
% 10.85/4.14  tff(c_27655, plain, (k4_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_27634, c_26151])).
% 10.85/4.14  tff(c_27683, plain, $false, inference(negUnitSimplification, [status(thm)], [c_129, c_27655])).
% 10.85/4.14  tff(c_27684, plain, (~r1_tarski('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_56])).
% 10.85/4.14  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.85/4.14  tff(c_52, plain, (![A_24, C_26, B_25]: (r1_tarski(k2_zfmisc_1(A_24, C_26), k2_zfmisc_1(B_25, C_26)) | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.85/4.14  tff(c_27937, plain, (![A_675, C_676, B_677]: (r1_tarski(k2_zfmisc_1(A_675, C_676), k2_zfmisc_1(B_677, C_676)) | ~r1_tarski(A_675, B_677))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.85/4.14  tff(c_28198, plain, (![A_694, B_695]: (r1_tarski(k2_zfmisc_1(A_694, B_695), k1_xboole_0) | ~r1_tarski(A_694, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_44, c_27937])).
% 10.85/4.14  tff(c_28211, plain, (![A_694, B_695]: (k4_xboole_0(k2_zfmisc_1(A_694, B_695), k1_xboole_0)=k1_xboole_0 | ~r1_tarski(A_694, k1_xboole_0))), inference(resolution, [status(thm)], [c_28198, c_34])).
% 10.85/4.14  tff(c_28228, plain, (![A_696, B_697]: (k2_zfmisc_1(A_696, B_697)=k1_xboole_0 | ~r1_tarski(A_696, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_28211])).
% 10.85/4.14  tff(c_28235, plain, (![A_14, B_697]: (k2_zfmisc_1(A_14, B_697)=k1_xboole_0 | k4_xboole_0(A_14, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_28228])).
% 10.85/4.14  tff(c_28247, plain, (![A_698, B_699]: (k2_zfmisc_1(A_698, B_699)=k1_xboole_0 | k1_xboole_0!=A_698)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_28235])).
% 10.85/4.14  tff(c_28323, plain, (k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_28247, c_58])).
% 10.85/4.14  tff(c_27685, plain, (r1_tarski('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_56])).
% 10.85/4.14  tff(c_27695, plain, (![A_641, B_642]: (k3_xboole_0(A_641, B_642)=A_641 | ~r1_tarski(A_641, B_642))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.85/4.14  tff(c_27702, plain, (k3_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(resolution, [status(thm)], [c_27685, c_27695])).
% 10.85/4.14  tff(c_29098, plain, (![A_732, C_733, B_734, D_735]: (k3_xboole_0(k2_zfmisc_1(A_732, C_733), k2_zfmisc_1(B_734, D_735))=k2_zfmisc_1(k3_xboole_0(A_732, B_734), k3_xboole_0(C_733, D_735)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.85/4.14  tff(c_36, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.85/4.14  tff(c_27735, plain, (k3_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_6', '#skF_7'))=k2_zfmisc_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_60, c_36])).
% 10.85/4.14  tff(c_29107, plain, (k2_zfmisc_1(k3_xboole_0('#skF_4', '#skF_6'), k3_xboole_0('#skF_5', '#skF_7'))=k2_zfmisc_1('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_29098, c_27735])).
% 10.85/4.14  tff(c_29165, plain, (k2_zfmisc_1('#skF_4', k3_xboole_0('#skF_5', '#skF_7'))=k2_zfmisc_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_27702, c_29107])).
% 10.85/4.14  tff(c_46, plain, (![A_21, B_22, C_23]: (~r1_tarski(k2_zfmisc_1(A_21, B_22), k2_zfmisc_1(A_21, C_23)) | r1_tarski(B_22, C_23) | k1_xboole_0=A_21)), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.85/4.14  tff(c_29289, plain, (![B_22]: (~r1_tarski(k2_zfmisc_1('#skF_4', B_22), k2_zfmisc_1('#skF_4', '#skF_5')) | r1_tarski(B_22, k3_xboole_0('#skF_5', '#skF_7')) | k1_xboole_0='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_29165, c_46])).
% 10.85/4.14  tff(c_33207, plain, (![B_843]: (~r1_tarski(k2_zfmisc_1('#skF_4', B_843), k2_zfmisc_1('#skF_4', '#skF_5')) | r1_tarski(B_843, k3_xboole_0('#skF_5', '#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_28323, c_29289])).
% 10.85/4.14  tff(c_33248, plain, (r1_tarski('#skF_5', k3_xboole_0('#skF_5', '#skF_7')) | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_33207])).
% 10.85/4.14  tff(c_33261, plain, (r1_tarski('#skF_5', k3_xboole_0('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_33248])).
% 10.85/4.14  tff(c_33290, plain, (k4_xboole_0('#skF_5', k3_xboole_0('#skF_5', '#skF_7'))=k1_xboole_0), inference(resolution, [status(thm)], [c_33261, c_34])).
% 10.85/4.14  tff(c_29286, plain, (![C_23]: (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_4', C_23)) | r1_tarski(k3_xboole_0('#skF_5', '#skF_7'), C_23) | k1_xboole_0='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_29165, c_46])).
% 10.85/4.14  tff(c_33497, plain, (![C_849]: (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_4', C_849)) | r1_tarski(k3_xboole_0('#skF_5', '#skF_7'), C_849))), inference(negUnitSimplification, [status(thm)], [c_28323, c_29286])).
% 10.85/4.14  tff(c_33538, plain, (r1_tarski(k3_xboole_0('#skF_5', '#skF_7'), '#skF_5') | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_33497])).
% 10.85/4.14  tff(c_33551, plain, (r1_tarski(k3_xboole_0('#skF_5', '#skF_7'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_33538])).
% 10.85/4.14  tff(c_27771, plain, (![B_651, A_652]: (B_651=A_652 | ~r1_tarski(B_651, A_652) | ~r1_tarski(A_652, B_651))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.85/4.14  tff(c_27780, plain, (![B_15, A_14]: (B_15=A_14 | ~r1_tarski(B_15, A_14) | k4_xboole_0(A_14, B_15)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_27771])).
% 10.85/4.14  tff(c_33564, plain, (k3_xboole_0('#skF_5', '#skF_7')='#skF_5' | k4_xboole_0('#skF_5', k3_xboole_0('#skF_5', '#skF_7'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_33551, c_27780])).
% 10.85/4.14  tff(c_33579, plain, (k3_xboole_0('#skF_5', '#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_33290, c_33564])).
% 10.85/4.14  tff(c_33742, plain, (![D_853]: (r2_hidden(D_853, '#skF_7') | ~r2_hidden(D_853, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_33579, c_10])).
% 10.85/4.14  tff(c_33773, plain, (![A_854]: (r1_tarski(A_854, '#skF_7') | ~r2_hidden('#skF_1'(A_854, '#skF_7'), '#skF_5'))), inference(resolution, [status(thm)], [c_33742, c_4])).
% 10.85/4.14  tff(c_33777, plain, (r1_tarski('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_6, c_33773])).
% 10.85/4.14  tff(c_33781, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27684, c_27684, c_33777])).
% 10.85/4.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.85/4.14  
% 10.85/4.14  Inference rules
% 10.85/4.14  ----------------------
% 10.85/4.14  #Ref     : 0
% 10.85/4.14  #Sup     : 8432
% 10.85/4.14  #Fact    : 0
% 10.85/4.14  #Define  : 0
% 10.85/4.14  #Split   : 18
% 10.85/4.14  #Chain   : 0
% 10.85/4.14  #Close   : 0
% 10.85/4.14  
% 10.85/4.14  Ordering : KBO
% 10.85/4.14  
% 10.85/4.14  Simplification rules
% 10.85/4.14  ----------------------
% 10.85/4.14  #Subsume      : 1130
% 10.85/4.14  #Demod        : 4955
% 10.85/4.14  #Tautology    : 5634
% 10.85/4.14  #SimpNegUnit  : 48
% 10.85/4.14  #BackRed      : 36
% 10.85/4.14  
% 10.85/4.14  #Partial instantiations: 0
% 10.85/4.14  #Strategies tried      : 1
% 10.85/4.14  
% 10.85/4.14  Timing (in seconds)
% 10.85/4.14  ----------------------
% 10.85/4.15  Preprocessing        : 0.31
% 10.85/4.15  Parsing              : 0.16
% 10.85/4.15  CNF conversion       : 0.02
% 10.85/4.15  Main loop            : 3.05
% 10.85/4.15  Inferencing          : 0.78
% 10.85/4.15  Reduction            : 1.21
% 10.85/4.15  Demodulation         : 0.90
% 10.96/4.15  BG Simplification    : 0.09
% 10.96/4.15  Subsumption          : 0.78
% 10.96/4.15  Abstraction          : 0.13
% 10.96/4.15  MUC search           : 0.00
% 10.96/4.15  Cooper               : 0.00
% 10.96/4.15  Total                : 3.40
% 10.96/4.15  Index Insertion      : 0.00
% 10.96/4.15  Index Deletion       : 0.00
% 10.96/4.15  Index Matching       : 0.00
% 10.96/4.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
