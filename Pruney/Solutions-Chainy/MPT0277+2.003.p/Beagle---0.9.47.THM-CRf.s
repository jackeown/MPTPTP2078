%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:20 EST 2020

% Result     : Theorem 32.72s
% Output     : CNFRefutation 32.72s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 524 expanded)
%              Number of leaves         :   29 ( 158 expanded)
%              Depth                    :    9
%              Number of atoms          :  243 (1304 expanded)
%              Number of equality atoms :  208 (1251 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff(f_45,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_67,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_195,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k4_xboole_0(A,k2_tarski(B,C)) = k1_xboole_0
      <=> ~ ( A != k1_xboole_0
            & A != k1_tarski(B)
            & A != k1_tarski(C)
            & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_142,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_73,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_144,axiom,(
    ! [A,B] : k4_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_zfmisc_1)).

tff(c_14,plain,(
    ! [A_11] : k2_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_153654,plain,(
    ! [A_15155,B_15156] : k4_xboole_0(A_15155,k2_xboole_0(A_15155,B_15156)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_153673,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_153654])).

tff(c_150125,plain,(
    ! [A_14997,B_14998] : k4_xboole_0(A_14997,k2_xboole_0(A_14997,B_14998)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_150144,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_150125])).

tff(c_379,plain,(
    ! [A_100,B_101] : k4_xboole_0(A_100,k2_xboole_0(A_100,B_101)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_398,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_379])).

tff(c_124,plain,
    ( k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) != k1_xboole_0
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_223,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_120,plain,
    ( k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) != k1_xboole_0
    | k1_tarski('#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_249,plain,(
    k1_tarski('#skF_8') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_116,plain,
    ( k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) != k1_xboole_0
    | k1_tarski('#skF_9') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_378,plain,(
    k1_tarski('#skF_9') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_112,plain,
    ( k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) != k1_xboole_0
    | k2_tarski('#skF_8','#skF_9') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_463,plain,(
    k2_tarski('#skF_8','#skF_9') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_130,plain,
    ( k2_tarski('#skF_5','#skF_6') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4'
    | k4_xboole_0('#skF_7',k2_tarski('#skF_8','#skF_9')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_1657,plain,(
    k4_xboole_0('#skF_7',k2_tarski('#skF_8','#skF_9')) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_130])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | k4_xboole_0(A_14,B_15) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8518,plain,(
    ! [B_312,C_313,A_314] :
      ( k2_tarski(B_312,C_313) = A_314
      | k1_tarski(C_313) = A_314
      | k1_tarski(B_312) = A_314
      | k1_xboole_0 = A_314
      | ~ r1_tarski(A_314,k2_tarski(B_312,C_313)) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_71752,plain,(
    ! [B_7403,C_7404,A_7405] :
      ( k2_tarski(B_7403,C_7404) = A_7405
      | k1_tarski(C_7404) = A_7405
      | k1_tarski(B_7403) = A_7405
      | k1_xboole_0 = A_7405
      | k4_xboole_0(A_7405,k2_tarski(B_7403,C_7404)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_8518])).

tff(c_71869,plain,
    ( k2_tarski('#skF_8','#skF_9') = '#skF_7'
    | k1_tarski('#skF_9') = '#skF_7'
    | k1_tarski('#skF_8') = '#skF_7'
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_1657,c_71752])).

tff(c_71921,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_223,c_249,c_378,c_463,c_71869])).

tff(c_71922,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k2_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_71953,plain,(
    k2_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_71922])).

tff(c_128,plain,
    ( k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) != k1_xboole_0
    | k4_xboole_0('#skF_7',k2_tarski('#skF_8','#skF_9')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_551,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_71954,plain,(
    k4_xboole_0('#skF_4','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_71953,c_551])).

tff(c_71957,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_398,c_71954])).

tff(c_71958,plain,
    ( k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_71922])).

tff(c_72290,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_71958])).

tff(c_36,plain,(
    ! [A_29] : k4_xboole_0(k1_xboole_0,A_29) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_72325,plain,(
    ! [A_29] : k4_xboole_0('#skF_4',A_29) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72290,c_72290,c_36])).

tff(c_72306,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72290,c_551])).

tff(c_72470,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72325,c_72306])).

tff(c_72471,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_71958])).

tff(c_72473,plain,(
    k1_tarski('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_72471])).

tff(c_84,plain,(
    ! [C_58,B_57] : r1_tarski(k1_tarski(C_58),k2_tarski(B_57,C_58)) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_637,plain,(
    ! [A_130,B_131] :
      ( k4_xboole_0(A_130,B_131) = k1_xboole_0
      | ~ r1_tarski(A_130,B_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_666,plain,(
    ! [C_58,B_57] : k4_xboole_0(k1_tarski(C_58),k2_tarski(B_57,C_58)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_84,c_637])).

tff(c_72501,plain,(
    ! [B_57] : k4_xboole_0('#skF_4',k2_tarski(B_57,'#skF_6')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_72473,c_666])).

tff(c_73069,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72501,c_551])).

tff(c_73070,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_72471])).

tff(c_90,plain,(
    ! [A_59,B_60] : k4_xboole_0(k1_tarski(A_59),k2_tarski(A_59,B_60)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_73102,plain,(
    ! [B_60] : k4_xboole_0('#skF_4',k2_tarski('#skF_5',B_60)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_73070,c_90])).

tff(c_73492,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73102,c_551])).

tff(c_73493,plain,(
    k4_xboole_0('#skF_7',k2_tarski('#skF_8','#skF_9')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_81086,plain,(
    ! [B_7657,C_7658,A_7659] :
      ( k2_tarski(B_7657,C_7658) = A_7659
      | k1_tarski(C_7658) = A_7659
      | k1_tarski(B_7657) = A_7659
      | k1_xboole_0 = A_7659
      | ~ r1_tarski(A_7659,k2_tarski(B_7657,C_7658)) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_147739,plain,(
    ! [B_14884,C_14885,A_14886] :
      ( k2_tarski(B_14884,C_14885) = A_14886
      | k1_tarski(C_14885) = A_14886
      | k1_tarski(B_14884) = A_14886
      | k1_xboole_0 = A_14886
      | k4_xboole_0(A_14886,k2_tarski(B_14884,C_14885)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_81086])).

tff(c_147874,plain,
    ( k2_tarski('#skF_8','#skF_9') = '#skF_7'
    | k1_tarski('#skF_9') = '#skF_7'
    | k1_tarski('#skF_8') = '#skF_7'
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_73493,c_147739])).

tff(c_147923,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_223,c_249,c_378,c_463,c_147874])).

tff(c_147925,plain,(
    k2_tarski('#skF_8','#skF_9') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_114,plain,
    ( k2_tarski('#skF_5','#skF_6') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4'
    | k2_tarski('#skF_8','#skF_9') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_148364,plain,
    ( k2_tarski('#skF_5','#skF_6') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_147925,c_114])).

tff(c_148365,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_148364])).

tff(c_148395,plain,(
    ! [A_29] : k4_xboole_0('#skF_4',A_29) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_148365,c_148365,c_36])).

tff(c_147924,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_148379,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_148365,c_147924])).

tff(c_148575,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_148395,c_148379])).

tff(c_148576,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k2_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_148364])).

tff(c_148965,plain,(
    k2_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_148576])).

tff(c_148966,plain,(
    k4_xboole_0('#skF_4','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_148965,c_147924])).

tff(c_148969,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_398,c_148966])).

tff(c_148970,plain,
    ( k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_148576])).

tff(c_148995,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_148970])).

tff(c_149019,plain,(
    ! [B_60] : k4_xboole_0('#skF_4',k2_tarski('#skF_5',B_60)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_148995,c_90])).

tff(c_149505,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_149019,c_147924])).

tff(c_149506,plain,(
    k1_tarski('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_148970])).

tff(c_148182,plain,(
    ! [A_14919,B_14920] :
      ( k4_xboole_0(A_14919,B_14920) = k1_xboole_0
      | ~ r1_tarski(A_14919,B_14920) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_148221,plain,(
    ! [C_58,B_57] : k4_xboole_0(k1_tarski(C_58),k2_tarski(B_57,C_58)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_84,c_148182])).

tff(c_149522,plain,(
    ! [B_57] : k4_xboole_0('#skF_4',k2_tarski(B_57,'#skF_6')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_149506,c_148221])).

tff(c_150057,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_149522,c_147924])).

tff(c_150059,plain,(
    k1_tarski('#skF_9') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_118,plain,
    ( k2_tarski('#skF_5','#skF_6') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_9') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_150340,plain,
    ( k2_tarski('#skF_5','#skF_6') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150059,c_118])).

tff(c_150341,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_150340])).

tff(c_150362,plain,(
    ! [A_29] : k4_xboole_0('#skF_4',A_29) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150341,c_150341,c_36])).

tff(c_150182,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_150344,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150341,c_150182])).

tff(c_150714,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_150362,c_150344])).

tff(c_150715,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k2_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_150340])).

tff(c_151918,plain,(
    k2_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_150715])).

tff(c_151919,plain,(
    k4_xboole_0('#skF_4','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_151918,c_150182])).

tff(c_151922,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_150144,c_151919])).

tff(c_151923,plain,
    ( k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_150715])).

tff(c_151925,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_151923])).

tff(c_151950,plain,(
    ! [B_60] : k4_xboole_0('#skF_4',k2_tarski('#skF_5',B_60)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_151925,c_90])).

tff(c_152497,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_151950,c_150182])).

tff(c_152498,plain,(
    k1_tarski('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_151923])).

tff(c_150722,plain,(
    ! [A_15041,B_15042] :
      ( k4_xboole_0(A_15041,B_15042) = k1_xboole_0
      | ~ r1_tarski(A_15041,B_15042) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_150764,plain,(
    ! [C_58,B_57] : k4_xboole_0(k1_tarski(C_58),k2_tarski(B_57,C_58)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_84,c_150722])).

tff(c_152521,plain,(
    ! [B_57] : k4_xboole_0('#skF_4',k2_tarski(B_57,'#skF_6')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_152498,c_150764])).

tff(c_153280,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_152521,c_150182])).

tff(c_153282,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_150058,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_153384,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_153282,c_150058])).

tff(c_153386,plain,(
    k1_tarski('#skF_8') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_122,plain,
    ( k2_tarski('#skF_5','#skF_6') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_153856,plain,
    ( k2_tarski('#skF_5','#skF_6') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_153386,c_122])).

tff(c_153857,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_153856])).

tff(c_153884,plain,(
    ! [A_29] : k4_xboole_0('#skF_4',A_29) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_153857,c_153857,c_36])).

tff(c_153385,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_153866,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_153857,c_153385])).

tff(c_154155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_153884,c_153866])).

tff(c_154156,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k2_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_153856])).

tff(c_155010,plain,(
    k2_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_154156])).

tff(c_155011,plain,(
    k4_xboole_0('#skF_4','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_155010,c_153385])).

tff(c_155014,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_153673,c_155011])).

tff(c_155015,plain,
    ( k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_154156])).

tff(c_155017,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_155015])).

tff(c_155030,plain,(
    ! [B_60] : k4_xboole_0('#skF_4',k2_tarski('#skF_5',B_60)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_155017,c_90])).

tff(c_155406,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_155030,c_153385])).

tff(c_155407,plain,(
    k1_tarski('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_155015])).

tff(c_155641,plain,(
    ! [B_15251] : r1_tarski('#skF_4',k2_tarski(B_15251,'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_155407,c_84])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = k1_xboole_0
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_155652,plain,(
    ! [B_15251] : k4_xboole_0('#skF_4',k2_tarski(B_15251,'#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_155641,c_20])).

tff(c_157225,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_155652,c_153385])).

tff(c_157227,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_157229,plain,(
    ! [A_11] : k2_xboole_0(A_11,'#skF_7') = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_157227,c_14])).

tff(c_30,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k2_xboole_0(A_23,B_24)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_157522,plain,(
    ! [A_15325,B_15326] : k4_xboole_0(A_15325,k2_xboole_0(A_15325,B_15326)) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157227,c_30])).

tff(c_157544,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_157229,c_157522])).

tff(c_126,plain,
    ( k2_tarski('#skF_5','#skF_6') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_157633,plain,
    ( k2_tarski('#skF_5','#skF_6') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | '#skF_7' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157227,c_157227,c_126])).

tff(c_157634,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_157633])).

tff(c_157231,plain,(
    ! [A_29] : k4_xboole_0('#skF_7',A_29) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157227,c_157227,c_36])).

tff(c_157647,plain,(
    ! [A_29] : k4_xboole_0('#skF_4',A_29) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157634,c_157634,c_157231])).

tff(c_157226,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_157346,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157227,c_157226])).

tff(c_157642,plain,(
    k4_xboole_0('#skF_4',k2_tarski('#skF_5','#skF_6')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157634,c_157346])).

tff(c_157920,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_157647,c_157642])).

tff(c_157921,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k2_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_157633])).

tff(c_158665,plain,(
    k2_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_157921])).

tff(c_158666,plain,(
    k4_xboole_0('#skF_4','#skF_4') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_158665,c_157346])).

tff(c_158669,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_157544,c_158666])).

tff(c_158670,plain,
    ( k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_157921])).

tff(c_158672,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_158670])).

tff(c_158007,plain,(
    ! [A_59,B_60] : k4_xboole_0(k1_tarski(A_59),k2_tarski(A_59,B_60)) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157227,c_90])).

tff(c_158694,plain,(
    ! [B_60] : k4_xboole_0('#skF_4',k2_tarski('#skF_5',B_60)) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_158672,c_158007])).

tff(c_159393,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_158694,c_157346])).

tff(c_159394,plain,(
    k1_tarski('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_158670])).

tff(c_158025,plain,(
    ! [A_15364,B_15365] :
      ( k4_xboole_0(A_15364,B_15365) = '#skF_7'
      | ~ r1_tarski(A_15364,B_15365) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157227,c_20])).

tff(c_158050,plain,(
    ! [C_58,B_57] : k4_xboole_0(k1_tarski(C_58),k2_tarski(B_57,C_58)) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_84,c_158025])).

tff(c_159414,plain,(
    ! [B_57] : k4_xboole_0('#skF_4',k2_tarski(B_57,'#skF_6')) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_159394,c_158050])).

tff(c_160169,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_159414,c_157346])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:21:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 32.72/21.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 32.72/21.06  
% 32.72/21.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 32.72/21.07  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_2
% 32.72/21.07  
% 32.72/21.07  %Foreground sorts:
% 32.72/21.07  
% 32.72/21.07  
% 32.72/21.07  %Background operators:
% 32.72/21.07  
% 32.72/21.07  
% 32.72/21.07  %Foreground operators:
% 32.72/21.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 32.72/21.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 32.72/21.07  tff(k1_tarski, type, k1_tarski: $i > $i).
% 32.72/21.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 32.72/21.07  tff('#skF_1', type, '#skF_1': $i > $i).
% 32.72/21.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 32.72/21.07  tff('#skF_7', type, '#skF_7': $i).
% 32.72/21.07  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 32.72/21.07  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 32.72/21.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 32.72/21.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 32.72/21.07  tff('#skF_5', type, '#skF_5': $i).
% 32.72/21.07  tff('#skF_6', type, '#skF_6': $i).
% 32.72/21.07  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 32.72/21.07  tff('#skF_9', type, '#skF_9': $i).
% 32.72/21.07  tff('#skF_8', type, '#skF_8': $i).
% 32.72/21.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 32.72/21.07  tff('#skF_4', type, '#skF_4': $i).
% 32.72/21.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 32.72/21.07  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 32.72/21.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 32.72/21.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 32.72/21.07  
% 32.72/21.09  tff(f_45, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 32.72/21.09  tff(f_67, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 32.72/21.09  tff(f_195, negated_conjecture, ~(![A, B, C]: ((k4_xboole_0(A, k2_tarski(B, C)) = k1_xboole_0) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_zfmisc_1)).
% 32.72/21.09  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 32.72/21.09  tff(f_142, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 32.72/21.09  tff(f_73, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 32.72/21.09  tff(f_144, axiom, (![A, B]: (k4_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_zfmisc_1)).
% 32.72/21.09  tff(c_14, plain, (![A_11]: (k2_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_45])).
% 32.72/21.09  tff(c_153654, plain, (![A_15155, B_15156]: (k4_xboole_0(A_15155, k2_xboole_0(A_15155, B_15156))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 32.72/21.09  tff(c_153673, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_153654])).
% 32.72/21.09  tff(c_150125, plain, (![A_14997, B_14998]: (k4_xboole_0(A_14997, k2_xboole_0(A_14997, B_14998))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 32.72/21.09  tff(c_150144, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_150125])).
% 32.72/21.09  tff(c_379, plain, (![A_100, B_101]: (k4_xboole_0(A_100, k2_xboole_0(A_100, B_101))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 32.72/21.09  tff(c_398, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_379])).
% 32.72/21.09  tff(c_124, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))!=k1_xboole_0 | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_195])).
% 32.72/21.09  tff(c_223, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_124])).
% 32.72/21.09  tff(c_120, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))!=k1_xboole_0 | k1_tarski('#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_195])).
% 32.72/21.09  tff(c_249, plain, (k1_tarski('#skF_8')!='#skF_7'), inference(splitLeft, [status(thm)], [c_120])).
% 32.72/21.09  tff(c_116, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))!=k1_xboole_0 | k1_tarski('#skF_9')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_195])).
% 32.72/21.09  tff(c_378, plain, (k1_tarski('#skF_9')!='#skF_7'), inference(splitLeft, [status(thm)], [c_116])).
% 32.72/21.09  tff(c_112, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))!=k1_xboole_0 | k2_tarski('#skF_8', '#skF_9')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_195])).
% 32.72/21.09  tff(c_463, plain, (k2_tarski('#skF_8', '#skF_9')!='#skF_7'), inference(splitLeft, [status(thm)], [c_112])).
% 32.72/21.09  tff(c_130, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4' | k4_xboole_0('#skF_7', k2_tarski('#skF_8', '#skF_9'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_195])).
% 32.72/21.09  tff(c_1657, plain, (k4_xboole_0('#skF_7', k2_tarski('#skF_8', '#skF_9'))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_130])).
% 32.72/21.09  tff(c_18, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | k4_xboole_0(A_14, B_15)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 32.72/21.09  tff(c_8518, plain, (![B_312, C_313, A_314]: (k2_tarski(B_312, C_313)=A_314 | k1_tarski(C_313)=A_314 | k1_tarski(B_312)=A_314 | k1_xboole_0=A_314 | ~r1_tarski(A_314, k2_tarski(B_312, C_313)))), inference(cnfTransformation, [status(thm)], [f_142])).
% 32.72/21.09  tff(c_71752, plain, (![B_7403, C_7404, A_7405]: (k2_tarski(B_7403, C_7404)=A_7405 | k1_tarski(C_7404)=A_7405 | k1_tarski(B_7403)=A_7405 | k1_xboole_0=A_7405 | k4_xboole_0(A_7405, k2_tarski(B_7403, C_7404))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_8518])).
% 32.72/21.09  tff(c_71869, plain, (k2_tarski('#skF_8', '#skF_9')='#skF_7' | k1_tarski('#skF_9')='#skF_7' | k1_tarski('#skF_8')='#skF_7' | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_1657, c_71752])).
% 32.72/21.09  tff(c_71921, plain, $false, inference(negUnitSimplification, [status(thm)], [c_223, c_249, c_378, c_463, c_71869])).
% 32.72/21.09  tff(c_71922, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_5')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k2_tarski('#skF_5', '#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_130])).
% 32.72/21.09  tff(c_71953, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_71922])).
% 32.72/21.09  tff(c_128, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))!=k1_xboole_0 | k4_xboole_0('#skF_7', k2_tarski('#skF_8', '#skF_9'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_195])).
% 32.72/21.09  tff(c_551, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_128])).
% 32.72/21.09  tff(c_71954, plain, (k4_xboole_0('#skF_4', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_71953, c_551])).
% 32.72/21.09  tff(c_71957, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_398, c_71954])).
% 32.72/21.09  tff(c_71958, plain, (k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_71922])).
% 32.72/21.09  tff(c_72290, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_71958])).
% 32.72/21.09  tff(c_36, plain, (![A_29]: (k4_xboole_0(k1_xboole_0, A_29)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_73])).
% 32.72/21.09  tff(c_72325, plain, (![A_29]: (k4_xboole_0('#skF_4', A_29)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72290, c_72290, c_36])).
% 32.72/21.09  tff(c_72306, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_72290, c_551])).
% 32.72/21.09  tff(c_72470, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72325, c_72306])).
% 32.72/21.09  tff(c_72471, plain, (k1_tarski('#skF_5')='#skF_4' | k1_tarski('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_71958])).
% 32.72/21.09  tff(c_72473, plain, (k1_tarski('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_72471])).
% 32.72/21.09  tff(c_84, plain, (![C_58, B_57]: (r1_tarski(k1_tarski(C_58), k2_tarski(B_57, C_58)))), inference(cnfTransformation, [status(thm)], [f_142])).
% 32.72/21.09  tff(c_637, plain, (![A_130, B_131]: (k4_xboole_0(A_130, B_131)=k1_xboole_0 | ~r1_tarski(A_130, B_131))), inference(cnfTransformation, [status(thm)], [f_53])).
% 32.72/21.09  tff(c_666, plain, (![C_58, B_57]: (k4_xboole_0(k1_tarski(C_58), k2_tarski(B_57, C_58))=k1_xboole_0)), inference(resolution, [status(thm)], [c_84, c_637])).
% 32.72/21.09  tff(c_72501, plain, (![B_57]: (k4_xboole_0('#skF_4', k2_tarski(B_57, '#skF_6'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_72473, c_666])).
% 32.72/21.09  tff(c_73069, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72501, c_551])).
% 32.72/21.09  tff(c_73070, plain, (k1_tarski('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_72471])).
% 32.72/21.09  tff(c_90, plain, (![A_59, B_60]: (k4_xboole_0(k1_tarski(A_59), k2_tarski(A_59, B_60))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_144])).
% 32.72/21.09  tff(c_73102, plain, (![B_60]: (k4_xboole_0('#skF_4', k2_tarski('#skF_5', B_60))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_73070, c_90])).
% 32.72/21.09  tff(c_73492, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73102, c_551])).
% 32.72/21.09  tff(c_73493, plain, (k4_xboole_0('#skF_7', k2_tarski('#skF_8', '#skF_9'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_128])).
% 32.72/21.09  tff(c_81086, plain, (![B_7657, C_7658, A_7659]: (k2_tarski(B_7657, C_7658)=A_7659 | k1_tarski(C_7658)=A_7659 | k1_tarski(B_7657)=A_7659 | k1_xboole_0=A_7659 | ~r1_tarski(A_7659, k2_tarski(B_7657, C_7658)))), inference(cnfTransformation, [status(thm)], [f_142])).
% 32.72/21.09  tff(c_147739, plain, (![B_14884, C_14885, A_14886]: (k2_tarski(B_14884, C_14885)=A_14886 | k1_tarski(C_14885)=A_14886 | k1_tarski(B_14884)=A_14886 | k1_xboole_0=A_14886 | k4_xboole_0(A_14886, k2_tarski(B_14884, C_14885))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_81086])).
% 32.72/21.09  tff(c_147874, plain, (k2_tarski('#skF_8', '#skF_9')='#skF_7' | k1_tarski('#skF_9')='#skF_7' | k1_tarski('#skF_8')='#skF_7' | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_73493, c_147739])).
% 32.72/21.09  tff(c_147923, plain, $false, inference(negUnitSimplification, [status(thm)], [c_223, c_249, c_378, c_463, c_147874])).
% 32.72/21.09  tff(c_147925, plain, (k2_tarski('#skF_8', '#skF_9')='#skF_7'), inference(splitRight, [status(thm)], [c_112])).
% 32.72/21.09  tff(c_114, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4' | k2_tarski('#skF_8', '#skF_9')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_195])).
% 32.72/21.09  tff(c_148364, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_147925, c_114])).
% 32.72/21.09  tff(c_148365, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_148364])).
% 32.72/21.09  tff(c_148395, plain, (![A_29]: (k4_xboole_0('#skF_4', A_29)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_148365, c_148365, c_36])).
% 32.72/21.09  tff(c_147924, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_112])).
% 32.72/21.09  tff(c_148379, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_148365, c_147924])).
% 32.72/21.09  tff(c_148575, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_148395, c_148379])).
% 32.72/21.09  tff(c_148576, plain, (k1_tarski('#skF_5')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k2_tarski('#skF_5', '#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_148364])).
% 32.72/21.09  tff(c_148965, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_148576])).
% 32.72/21.09  tff(c_148966, plain, (k4_xboole_0('#skF_4', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_148965, c_147924])).
% 32.72/21.09  tff(c_148969, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_398, c_148966])).
% 32.72/21.09  tff(c_148970, plain, (k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_148576])).
% 32.72/21.09  tff(c_148995, plain, (k1_tarski('#skF_5')='#skF_4'), inference(splitLeft, [status(thm)], [c_148970])).
% 32.72/21.09  tff(c_149019, plain, (![B_60]: (k4_xboole_0('#skF_4', k2_tarski('#skF_5', B_60))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_148995, c_90])).
% 32.72/21.09  tff(c_149505, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_149019, c_147924])).
% 32.72/21.09  tff(c_149506, plain, (k1_tarski('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_148970])).
% 32.72/21.09  tff(c_148182, plain, (![A_14919, B_14920]: (k4_xboole_0(A_14919, B_14920)=k1_xboole_0 | ~r1_tarski(A_14919, B_14920))), inference(cnfTransformation, [status(thm)], [f_53])).
% 32.72/21.09  tff(c_148221, plain, (![C_58, B_57]: (k4_xboole_0(k1_tarski(C_58), k2_tarski(B_57, C_58))=k1_xboole_0)), inference(resolution, [status(thm)], [c_84, c_148182])).
% 32.72/21.09  tff(c_149522, plain, (![B_57]: (k4_xboole_0('#skF_4', k2_tarski(B_57, '#skF_6'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_149506, c_148221])).
% 32.72/21.09  tff(c_150057, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_149522, c_147924])).
% 32.72/21.09  tff(c_150059, plain, (k1_tarski('#skF_9')='#skF_7'), inference(splitRight, [status(thm)], [c_116])).
% 32.72/21.09  tff(c_118, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4' | k1_tarski('#skF_9')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_195])).
% 32.72/21.09  tff(c_150340, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_150059, c_118])).
% 32.72/21.09  tff(c_150341, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_150340])).
% 32.72/21.09  tff(c_150362, plain, (![A_29]: (k4_xboole_0('#skF_4', A_29)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_150341, c_150341, c_36])).
% 32.72/21.09  tff(c_150182, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_128])).
% 32.72/21.09  tff(c_150344, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_150341, c_150182])).
% 32.72/21.09  tff(c_150714, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_150362, c_150344])).
% 32.72/21.09  tff(c_150715, plain, (k1_tarski('#skF_5')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k2_tarski('#skF_5', '#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_150340])).
% 32.72/21.09  tff(c_151918, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_150715])).
% 32.72/21.09  tff(c_151919, plain, (k4_xboole_0('#skF_4', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_151918, c_150182])).
% 32.72/21.09  tff(c_151922, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_150144, c_151919])).
% 32.72/21.09  tff(c_151923, plain, (k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_150715])).
% 32.72/21.09  tff(c_151925, plain, (k1_tarski('#skF_5')='#skF_4'), inference(splitLeft, [status(thm)], [c_151923])).
% 32.72/21.09  tff(c_151950, plain, (![B_60]: (k4_xboole_0('#skF_4', k2_tarski('#skF_5', B_60))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_151925, c_90])).
% 32.72/21.09  tff(c_152497, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_151950, c_150182])).
% 32.72/21.09  tff(c_152498, plain, (k1_tarski('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_151923])).
% 32.72/21.09  tff(c_150722, plain, (![A_15041, B_15042]: (k4_xboole_0(A_15041, B_15042)=k1_xboole_0 | ~r1_tarski(A_15041, B_15042))), inference(cnfTransformation, [status(thm)], [f_53])).
% 32.72/21.09  tff(c_150764, plain, (![C_58, B_57]: (k4_xboole_0(k1_tarski(C_58), k2_tarski(B_57, C_58))=k1_xboole_0)), inference(resolution, [status(thm)], [c_84, c_150722])).
% 32.72/21.09  tff(c_152521, plain, (![B_57]: (k4_xboole_0('#skF_4', k2_tarski(B_57, '#skF_6'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_152498, c_150764])).
% 32.72/21.09  tff(c_153280, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_152521, c_150182])).
% 32.72/21.09  tff(c_153282, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_128])).
% 32.72/21.09  tff(c_150058, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_116])).
% 32.72/21.09  tff(c_153384, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_153282, c_150058])).
% 32.72/21.09  tff(c_153386, plain, (k1_tarski('#skF_8')='#skF_7'), inference(splitRight, [status(thm)], [c_120])).
% 32.72/21.09  tff(c_122, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4' | k1_tarski('#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_195])).
% 32.72/21.09  tff(c_153856, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_153386, c_122])).
% 32.72/21.09  tff(c_153857, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_153856])).
% 32.72/21.09  tff(c_153884, plain, (![A_29]: (k4_xboole_0('#skF_4', A_29)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_153857, c_153857, c_36])).
% 32.72/21.09  tff(c_153385, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_120])).
% 32.72/21.09  tff(c_153866, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_153857, c_153385])).
% 32.72/21.09  tff(c_154155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_153884, c_153866])).
% 32.72/21.09  tff(c_154156, plain, (k1_tarski('#skF_5')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k2_tarski('#skF_5', '#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_153856])).
% 32.72/21.09  tff(c_155010, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_154156])).
% 32.72/21.09  tff(c_155011, plain, (k4_xboole_0('#skF_4', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_155010, c_153385])).
% 32.72/21.09  tff(c_155014, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_153673, c_155011])).
% 32.72/21.09  tff(c_155015, plain, (k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_154156])).
% 32.72/21.09  tff(c_155017, plain, (k1_tarski('#skF_5')='#skF_4'), inference(splitLeft, [status(thm)], [c_155015])).
% 32.72/21.09  tff(c_155030, plain, (![B_60]: (k4_xboole_0('#skF_4', k2_tarski('#skF_5', B_60))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_155017, c_90])).
% 32.72/21.09  tff(c_155406, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_155030, c_153385])).
% 32.72/21.09  tff(c_155407, plain, (k1_tarski('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_155015])).
% 32.72/21.09  tff(c_155641, plain, (![B_15251]: (r1_tarski('#skF_4', k2_tarski(B_15251, '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_155407, c_84])).
% 32.72/21.09  tff(c_20, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=k1_xboole_0 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 32.72/21.09  tff(c_155652, plain, (![B_15251]: (k4_xboole_0('#skF_4', k2_tarski(B_15251, '#skF_6'))=k1_xboole_0)), inference(resolution, [status(thm)], [c_155641, c_20])).
% 32.72/21.09  tff(c_157225, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_155652, c_153385])).
% 32.72/21.09  tff(c_157227, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_124])).
% 32.72/21.09  tff(c_157229, plain, (![A_11]: (k2_xboole_0(A_11, '#skF_7')=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_157227, c_14])).
% 32.72/21.09  tff(c_30, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k2_xboole_0(A_23, B_24))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 32.72/21.09  tff(c_157522, plain, (![A_15325, B_15326]: (k4_xboole_0(A_15325, k2_xboole_0(A_15325, B_15326))='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_157227, c_30])).
% 32.72/21.09  tff(c_157544, plain, (![A_11]: (k4_xboole_0(A_11, A_11)='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_157229, c_157522])).
% 32.72/21.09  tff(c_126, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_195])).
% 32.72/21.09  tff(c_157633, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4' | '#skF_7'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_157227, c_157227, c_126])).
% 32.72/21.09  tff(c_157634, plain, ('#skF_7'='#skF_4'), inference(splitLeft, [status(thm)], [c_157633])).
% 32.72/21.09  tff(c_157231, plain, (![A_29]: (k4_xboole_0('#skF_7', A_29)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_157227, c_157227, c_36])).
% 32.72/21.09  tff(c_157647, plain, (![A_29]: (k4_xboole_0('#skF_4', A_29)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_157634, c_157634, c_157231])).
% 32.72/21.09  tff(c_157226, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_124])).
% 32.72/21.09  tff(c_157346, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_157227, c_157226])).
% 32.72/21.09  tff(c_157642, plain, (k4_xboole_0('#skF_4', k2_tarski('#skF_5', '#skF_6'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_157634, c_157346])).
% 32.72/21.09  tff(c_157920, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_157647, c_157642])).
% 32.72/21.09  tff(c_157921, plain, (k1_tarski('#skF_5')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k2_tarski('#skF_5', '#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_157633])).
% 32.72/21.09  tff(c_158665, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_157921])).
% 32.72/21.09  tff(c_158666, plain, (k4_xboole_0('#skF_4', '#skF_4')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_158665, c_157346])).
% 32.72/21.09  tff(c_158669, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_157544, c_158666])).
% 32.72/21.09  tff(c_158670, plain, (k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_157921])).
% 32.72/21.09  tff(c_158672, plain, (k1_tarski('#skF_5')='#skF_4'), inference(splitLeft, [status(thm)], [c_158670])).
% 32.72/21.09  tff(c_158007, plain, (![A_59, B_60]: (k4_xboole_0(k1_tarski(A_59), k2_tarski(A_59, B_60))='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_157227, c_90])).
% 32.72/21.09  tff(c_158694, plain, (![B_60]: (k4_xboole_0('#skF_4', k2_tarski('#skF_5', B_60))='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_158672, c_158007])).
% 32.72/21.09  tff(c_159393, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_158694, c_157346])).
% 32.72/21.09  tff(c_159394, plain, (k1_tarski('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_158670])).
% 32.72/21.09  tff(c_158025, plain, (![A_15364, B_15365]: (k4_xboole_0(A_15364, B_15365)='#skF_7' | ~r1_tarski(A_15364, B_15365))), inference(demodulation, [status(thm), theory('equality')], [c_157227, c_20])).
% 32.72/21.09  tff(c_158050, plain, (![C_58, B_57]: (k4_xboole_0(k1_tarski(C_58), k2_tarski(B_57, C_58))='#skF_7')), inference(resolution, [status(thm)], [c_84, c_158025])).
% 32.72/21.09  tff(c_159414, plain, (![B_57]: (k4_xboole_0('#skF_4', k2_tarski(B_57, '#skF_6'))='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_159394, c_158050])).
% 32.72/21.09  tff(c_160169, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_159414, c_157346])).
% 32.72/21.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 32.72/21.09  
% 32.72/21.09  Inference rules
% 32.72/21.09  ----------------------
% 32.72/21.09  #Ref     : 14
% 32.72/21.09  #Sup     : 37445
% 32.72/21.09  #Fact    : 0
% 32.72/21.09  #Define  : 0
% 32.72/21.09  #Split   : 56
% 32.72/21.09  #Chain   : 0
% 32.72/21.09  #Close   : 0
% 32.72/21.09  
% 32.72/21.09  Ordering : KBO
% 32.72/21.09  
% 32.72/21.09  Simplification rules
% 32.72/21.09  ----------------------
% 32.72/21.09  #Subsume      : 8289
% 32.72/21.09  #Demod        : 44979
% 32.72/21.09  #Tautology    : 18461
% 32.72/21.09  #SimpNegUnit  : 1809
% 32.72/21.09  #BackRed      : 192
% 32.72/21.09  
% 32.72/21.09  #Partial instantiations: 13296
% 32.72/21.09  #Strategies tried      : 1
% 32.72/21.09  
% 32.72/21.09  Timing (in seconds)
% 32.72/21.09  ----------------------
% 32.95/21.09  Preprocessing        : 0.38
% 32.95/21.09  Parsing              : 0.20
% 32.95/21.09  CNF conversion       : 0.03
% 32.95/21.09  Main loop            : 19.92
% 32.95/21.09  Inferencing          : 2.82
% 32.95/21.09  Reduction            : 11.92
% 32.95/21.09  Demodulation         : 10.28
% 32.95/21.09  BG Simplification    : 0.27
% 32.95/21.09  Subsumption          : 4.17
% 32.95/21.09  Abstraction          : 0.67
% 32.95/21.09  MUC search           : 0.00
% 32.95/21.09  Cooper               : 0.00
% 32.95/21.09  Total                : 20.35
% 32.95/21.09  Index Insertion      : 0.00
% 32.95/21.09  Index Deletion       : 0.00
% 32.95/21.09  Index Matching       : 0.00
% 32.95/21.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
