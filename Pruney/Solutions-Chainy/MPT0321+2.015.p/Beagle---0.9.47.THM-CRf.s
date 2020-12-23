%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:15 EST 2020

% Result     : Theorem 24.64s
% Output     : CNFRefutation 24.83s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 595 expanded)
%              Number of leaves         :   28 ( 209 expanded)
%              Depth                    :   15
%              Number of atoms          :  232 (1091 expanded)
%              Number of equality atoms :  171 ( 824 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_109,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k4_xboole_0(A,B),C) = k4_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k4_xboole_0(A,B)) = k4_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
          | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
        & ~ r1_tarski(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_69,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_55,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_94,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k4_xboole_0(B,A)
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_50,plain,
    ( '#skF_6' != '#skF_4'
    | '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_75,plain,(
    '#skF_5' != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_2561,plain,(
    ! [A_162,C_163,B_164] : k4_xboole_0(k2_zfmisc_1(A_162,C_163),k2_zfmisc_1(B_164,C_163)) = k2_zfmisc_1(k4_xboole_0(A_162,B_164),C_163) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_56,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_663,plain,(
    ! [C_86,A_87,B_88] : k4_xboole_0(k2_zfmisc_1(C_86,A_87),k2_zfmisc_1(C_86,B_88)) = k2_zfmisc_1(C_86,k4_xboole_0(A_87,B_88)) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_695,plain,(
    ! [B_88] : k4_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',B_88)) = k2_zfmisc_1('#skF_5',k4_xboole_0('#skF_6',B_88)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_663])).

tff(c_2581,plain,(
    k2_zfmisc_1(k4_xboole_0('#skF_3','#skF_5'),'#skF_4') = k2_zfmisc_1('#skF_5',k4_xboole_0('#skF_6','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2561,c_695])).

tff(c_46,plain,(
    ! [A_33,C_35,B_34] : k4_xboole_0(k2_zfmisc_1(A_33,C_35),k2_zfmisc_1(B_34,C_35)) = k2_zfmisc_1(k4_xboole_0(A_33,B_34),C_35) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | k4_xboole_0(A_12,B_13) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_882,plain,(
    ! [B_101,A_102,C_103] :
      ( ~ r1_tarski(k2_zfmisc_1(B_101,A_102),k2_zfmisc_1(C_103,A_102))
      | r1_tarski(B_101,C_103)
      | k1_xboole_0 = A_102 ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_908,plain,(
    ! [B_101,C_103,A_102] :
      ( r1_tarski(B_101,C_103)
      | k1_xboole_0 = A_102
      | k4_xboole_0(k2_zfmisc_1(B_101,A_102),k2_zfmisc_1(C_103,A_102)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_882])).

tff(c_8371,plain,(
    ! [B_288,C_289,A_290] :
      ( r1_tarski(B_288,C_289)
      | k1_xboole_0 = A_290
      | k2_zfmisc_1(k4_xboole_0(B_288,C_289),A_290) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_908])).

tff(c_8380,plain,
    ( r1_tarski('#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_4'
    | k2_zfmisc_1('#skF_5',k4_xboole_0('#skF_6','#skF_4')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2581,c_8371])).

tff(c_8449,plain,
    ( r1_tarski('#skF_3','#skF_5')
    | k2_zfmisc_1('#skF_5',k4_xboole_0('#skF_6','#skF_4')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_8380])).

tff(c_8467,plain,(
    k2_zfmisc_1('#skF_5',k4_xboole_0('#skF_6','#skF_4')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_8449])).

tff(c_38,plain,(
    ! [B_25] : k2_zfmisc_1(k1_xboole_0,B_25) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_888,plain,(
    ! [C_103] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1(C_103,'#skF_6'))
      | r1_tarski('#skF_5',C_103)
      | k1_xboole_0 = '#skF_6' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_882])).

tff(c_1900,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_888])).

tff(c_36,plain,(
    ! [A_24] : k2_zfmisc_1(A_24,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1928,plain,(
    ! [A_24] : k2_zfmisc_1(A_24,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1900,c_1900,c_36])).

tff(c_2318,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1928,c_56])).

tff(c_333,plain,(
    ! [B_62,A_63] :
      ( k1_xboole_0 = B_62
      | k1_xboole_0 = A_63
      | k2_zfmisc_1(A_63,B_62) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_336,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k2_zfmisc_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_333])).

tff(c_366,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_336])).

tff(c_1916,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1900,c_366])).

tff(c_2466,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2318,c_1916])).

tff(c_2468,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_888])).

tff(c_4379,plain,(
    ! [A_201] : k4_xboole_0(k2_zfmisc_1(A_201,'#skF_6'),k2_zfmisc_1('#skF_3','#skF_4')) = k2_zfmisc_1(k4_xboole_0(A_201,'#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_2561])).

tff(c_48,plain,(
    ! [C_35,A_33,B_34] : k4_xboole_0(k2_zfmisc_1(C_35,A_33),k2_zfmisc_1(C_35,B_34)) = k2_zfmisc_1(C_35,k4_xboole_0(A_33,B_34)) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4416,plain,(
    k2_zfmisc_1(k4_xboole_0('#skF_3','#skF_5'),'#skF_6') = k2_zfmisc_1('#skF_3',k4_xboole_0('#skF_6','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4379,c_48])).

tff(c_8370,plain,(
    ! [B_101,C_103,A_102] :
      ( r1_tarski(B_101,C_103)
      | k1_xboole_0 = A_102
      | k2_zfmisc_1(k4_xboole_0(B_101,C_103),A_102) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_908])).

tff(c_9010,plain,
    ( r1_tarski('#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_6'
    | k2_zfmisc_1('#skF_3',k4_xboole_0('#skF_6','#skF_4')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4416,c_8370])).

tff(c_9112,plain,
    ( r1_tarski('#skF_3','#skF_5')
    | k2_zfmisc_1('#skF_3',k4_xboole_0('#skF_6','#skF_4')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_2468,c_9010])).

tff(c_9127,plain,(
    k2_zfmisc_1('#skF_3',k4_xboole_0('#skF_6','#skF_4')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_9112])).

tff(c_26,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_14,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_191,plain,(
    ! [A_47,B_48] :
      ( k4_xboole_0(A_47,B_48) = k1_xboole_0
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_199,plain,(
    ! [B_11] : k4_xboole_0(B_11,B_11) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_191])).

tff(c_395,plain,(
    ! [A_72,B_73] : k4_xboole_0(A_72,k4_xboole_0(A_72,B_73)) = k3_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_430,plain,(
    ! [B_11] : k4_xboole_0(B_11,k1_xboole_0) = k3_xboole_0(B_11,B_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_395])).

tff(c_440,plain,(
    ! [B_11] : k3_xboole_0(B_11,B_11) = B_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_430])).

tff(c_28,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_24,plain,(
    ! [A_17,B_18] : r1_tarski(k4_xboole_0(A_17,B_18),A_17) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_379,plain,(
    ! [B_70,A_71] :
      ( B_70 = A_71
      | ~ r1_tarski(B_70,A_71)
      | ~ r1_tarski(A_71,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4090,plain,(
    ! [B_195,A_196] :
      ( B_195 = A_196
      | ~ r1_tarski(B_195,A_196)
      | k4_xboole_0(A_196,B_195) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_379])).

tff(c_4114,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = A_17
      | k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_4090])).

tff(c_4131,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = A_17
      | k3_xboole_0(A_17,B_18) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_4114])).

tff(c_44,plain,(
    ! [A_29,C_31,B_30,D_32] : k3_xboole_0(k2_zfmisc_1(A_29,C_31),k2_zfmisc_1(B_30,D_32)) = k2_zfmisc_1(k3_xboole_0(A_29,B_30),k3_xboole_0(C_31,D_32)) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2588,plain,(
    ! [A_162,C_163,B_164] : k4_xboole_0(k2_zfmisc_1(A_162,C_163),k2_zfmisc_1(k4_xboole_0(A_162,B_164),C_163)) = k3_xboole_0(k2_zfmisc_1(A_162,C_163),k2_zfmisc_1(B_164,C_163)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2561,c_28])).

tff(c_11977,plain,(
    ! [A_337,C_338,B_339] : k4_xboole_0(k2_zfmisc_1(A_337,C_338),k2_zfmisc_1(k4_xboole_0(A_337,B_339),C_338)) = k2_zfmisc_1(k3_xboole_0(A_337,B_339),C_338) ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_44,c_2588])).

tff(c_12141,plain,(
    ! [A_17,C_338,B_18] :
      ( k4_xboole_0(k2_zfmisc_1(A_17,C_338),k2_zfmisc_1(A_17,C_338)) = k2_zfmisc_1(k3_xboole_0(A_17,B_18),C_338)
      | k3_xboole_0(A_17,B_18) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4131,c_11977])).

tff(c_12270,plain,(
    ! [A_340,B_341,C_342] :
      ( k2_zfmisc_1(k3_xboole_0(A_340,B_341),C_342) = k1_xboole_0
      | k3_xboole_0(A_340,B_341) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_199,c_48,c_12141])).

tff(c_12489,plain,(
    ! [B_11,C_342] :
      ( k2_zfmisc_1(B_11,C_342) = k1_xboole_0
      | k3_xboole_0(B_11,B_11) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_12270])).

tff(c_12568,plain,(
    ! [B_343,C_344] :
      ( k2_zfmisc_1(B_343,C_344) = k1_xboole_0
      | k1_xboole_0 != B_343 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_12489])).

tff(c_12642,plain,
    ( k2_zfmisc_1('#skF_3',k4_xboole_0('#skF_6','#skF_4')) = k1_xboole_0
    | k4_xboole_0('#skF_3','#skF_5') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12568,c_4416])).

tff(c_12944,plain,(
    k4_xboole_0('#skF_3','#skF_5') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_9127,c_12642])).

tff(c_11976,plain,(
    ! [A_162,C_163,B_164] : k4_xboole_0(k2_zfmisc_1(A_162,C_163),k2_zfmisc_1(k4_xboole_0(A_162,B_164),C_163)) = k2_zfmisc_1(k3_xboole_0(A_162,B_164),C_163) ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_44,c_2588])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4419,plain,(
    ! [A_201] : k4_xboole_0(k2_zfmisc_1(A_201,'#skF_6'),k2_zfmisc_1(k4_xboole_0(A_201,'#skF_5'),'#skF_6')) = k3_xboole_0(k2_zfmisc_1(A_201,'#skF_6'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4379,c_28])).

tff(c_4466,plain,(
    ! [A_201] : k4_xboole_0(k2_zfmisc_1(A_201,'#skF_6'),k2_zfmisc_1(k4_xboole_0(A_201,'#skF_5'),'#skF_6')) = k2_zfmisc_1(k3_xboole_0(A_201,'#skF_3'),k3_xboole_0('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_44,c_4419])).

tff(c_52444,plain,(
    ! [A_678] : k2_zfmisc_1(k3_xboole_0(A_678,'#skF_3'),k3_xboole_0('#skF_4','#skF_6')) = k2_zfmisc_1(k3_xboole_0(A_678,'#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11976,c_4466])).

tff(c_3334,plain,(
    ! [A_178,C_179,B_180,D_181] : k3_xboole_0(k2_zfmisc_1(A_178,C_179),k2_zfmisc_1(B_180,D_181)) = k2_zfmisc_1(k3_xboole_0(A_178,B_180),k3_xboole_0(C_179,D_181)) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_411,plain,(
    ! [A_72,B_73] : r1_tarski(k3_xboole_0(A_72,B_73),A_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_395,c_24])).

tff(c_3376,plain,(
    ! [A_178,B_180,C_179,D_181] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_178,B_180),k3_xboole_0(C_179,D_181)),k2_zfmisc_1(A_178,C_179)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3334,c_411])).

tff(c_68140,plain,(
    ! [A_795] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_795,'#skF_5'),'#skF_6'),k2_zfmisc_1(A_795,'#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_52444,c_3376])).

tff(c_68291,plain,(
    r1_tarski(k2_zfmisc_1('#skF_5','#skF_6'),k2_zfmisc_1('#skF_5','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_68140])).

tff(c_68334,plain,(
    r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_68291])).

tff(c_42,plain,(
    ! [B_27,A_26,C_28] :
      ( ~ r1_tarski(k2_zfmisc_1(B_27,A_26),k2_zfmisc_1(C_28,A_26))
      | r1_tarski(B_27,C_28)
      | k1_xboole_0 = A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_68349,plain,
    ( r1_tarski('#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_68334,c_42])).

tff(c_68375,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_68349])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(A_12,B_13) = k1_xboole_0
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_68395,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_68375,c_18])).

tff(c_68409,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12944,c_68395])).

tff(c_68410,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_9112])).

tff(c_68432,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_68410,c_18])).

tff(c_68444,plain,(
    k2_zfmisc_1('#skF_5',k4_xboole_0('#skF_6','#skF_4')) = k2_zfmisc_1(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68432,c_2581])).

tff(c_68446,plain,(
    k2_zfmisc_1('#skF_5',k4_xboole_0('#skF_6','#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_68444])).

tff(c_68448,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8467,c_68446])).

tff(c_68449,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_8449])).

tff(c_10,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_68458,plain,
    ( '#skF_5' = '#skF_3'
    | ~ r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_68449,c_10])).

tff(c_68470,plain,(
    ~ r1_tarski('#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_68458])).

tff(c_68471,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_68449,c_18])).

tff(c_198,plain,(
    ! [A_17,B_18] : k4_xboole_0(k4_xboole_0(A_17,B_18),A_17) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_191])).

tff(c_420,plain,(
    ! [A_17,B_18] : k4_xboole_0(k4_xboole_0(A_17,B_18),k1_xboole_0) = k3_xboole_0(k4_xboole_0(A_17,B_18),A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_395])).

tff(c_1071,plain,(
    ! [A_115,B_116] : k3_xboole_0(k4_xboole_0(A_115,B_116),A_115) = k4_xboole_0(A_115,B_116) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_420])).

tff(c_1143,plain,(
    ! [A_1,B_116] : k3_xboole_0(A_1,k4_xboole_0(A_1,B_116)) = k4_xboole_0(A_1,B_116) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1071])).

tff(c_4136,plain,(
    ! [A_197,B_198] :
      ( k4_xboole_0(A_197,B_198) = A_197
      | k3_xboole_0(A_197,B_198) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_4114])).

tff(c_4196,plain,(
    ! [A_197,B_21] :
      ( k3_xboole_0(A_197,B_21) = A_197
      | k3_xboole_0(A_197,k4_xboole_0(A_197,B_21)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4136,c_28])).

tff(c_4286,plain,(
    ! [A_197,B_21] :
      ( k3_xboole_0(A_197,B_21) = A_197
      | k4_xboole_0(A_197,B_21) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1143,c_4196])).

tff(c_68572,plain,(
    k3_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_68471,c_4286])).

tff(c_70666,plain,(
    ! [A_162,C_163,B_164] : k4_xboole_0(k2_zfmisc_1(A_162,C_163),k2_zfmisc_1(k4_xboole_0(A_162,B_164),C_163)) = k2_zfmisc_1(k3_xboole_0(A_162,B_164),C_163) ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_44,c_2588])).

tff(c_1190,plain,(
    ! [A_118,B_119,C_120] :
      ( ~ r1_tarski(k2_zfmisc_1(A_118,B_119),k2_zfmisc_1(A_118,C_120))
      | r1_tarski(B_119,C_120)
      | k1_xboole_0 = A_118 ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1196,plain,(
    ! [C_120] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5',C_120))
      | r1_tarski('#skF_6',C_120)
      | k1_xboole_0 = '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_1190])).

tff(c_1336,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1196])).

tff(c_1362,plain,(
    ! [B_25] : k2_zfmisc_1('#skF_5',B_25) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1336,c_1336,c_38])).

tff(c_1697,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1362,c_56])).

tff(c_1351,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1336,c_366])).

tff(c_1897,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1697,c_1351])).

tff(c_1899,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1196])).

tff(c_68450,plain,(
    k2_zfmisc_1('#skF_5',k4_xboole_0('#skF_6','#skF_4')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_8449])).

tff(c_34,plain,(
    ! [B_25,A_24] :
      ( k1_xboole_0 = B_25
      | k1_xboole_0 = A_24
      | k2_zfmisc_1(A_24,B_25) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_69538,plain,
    ( k4_xboole_0('#skF_6','#skF_4') = k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_68450,c_34])).

tff(c_69586,plain,(
    k4_xboole_0('#skF_6','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1899,c_69538])).

tff(c_414,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k3_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,k4_xboole_0(A_20,B_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_395])).

tff(c_6289,plain,(
    ! [A_246,B_247] : k4_xboole_0(A_246,k3_xboole_0(A_246,B_247)) = k4_xboole_0(A_246,B_247) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1143,c_414])).

tff(c_6409,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_6289])).

tff(c_474,plain,(
    ! [A_75,B_76] : r1_tarski(k3_xboole_0(A_75,B_76),A_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_395,c_24])).

tff(c_500,plain,(
    ! [B_77,A_78] : r1_tarski(k3_xboole_0(B_77,A_78),A_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_474])).

tff(c_6694,plain,(
    ! [B_251,A_252] :
      ( k3_xboole_0(B_251,A_252) = A_252
      | ~ r1_tarski(A_252,k3_xboole_0(B_251,A_252)) ) ),
    inference(resolution,[status(thm)],[c_500,c_10])).

tff(c_6734,plain,(
    ! [B_251,A_12] :
      ( k3_xboole_0(B_251,A_12) = A_12
      | k4_xboole_0(A_12,k3_xboole_0(B_251,A_12)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_6694])).

tff(c_6770,plain,(
    ! [B_251,A_12] :
      ( k3_xboole_0(B_251,A_12) = A_12
      | k4_xboole_0(A_12,B_251) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6409,c_6734])).

tff(c_69701,plain,(
    k3_xboole_0('#skF_4','#skF_6') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_69586,c_6770])).

tff(c_97615,plain,(
    ! [A_1074] : k2_zfmisc_1(k3_xboole_0(A_1074,'#skF_5'),'#skF_6') = k2_zfmisc_1(k3_xboole_0(A_1074,'#skF_3'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70666,c_69701,c_4466])).

tff(c_97849,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_5','#skF_3'),'#skF_6') = k2_zfmisc_1('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_97615])).

tff(c_97913,plain,(
    k2_zfmisc_1('#skF_3','#skF_6') = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68572,c_56,c_2,c_97849])).

tff(c_2467,plain,(
    ! [C_103] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1(C_103,'#skF_6'))
      | r1_tarski('#skF_5',C_103) ) ),
    inference(splitRight,[status(thm)],[c_888])).

tff(c_97995,plain,
    ( ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_3','#skF_4'))
    | r1_tarski('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_97913,c_2467])).

tff(c_98081,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_97995])).

tff(c_98083,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68470,c_98081])).

tff(c_98085,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_336])).

tff(c_98098,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_98085,c_34])).

tff(c_98104,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_52,c_98098])).

tff(c_98105,plain,(
    '#skF_6' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_98227,plain,(
    ! [A_1084,B_1085] :
      ( k4_xboole_0(A_1084,B_1085) = k1_xboole_0
      | ~ r1_tarski(A_1084,B_1085) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_98235,plain,(
    ! [B_11] : k4_xboole_0(B_11,B_11) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_98227])).

tff(c_98106,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_98220,plain,(
    k2_zfmisc_1('#skF_3','#skF_6') = k2_zfmisc_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98106,c_56])).

tff(c_98826,plain,(
    ! [A_1128,C_1129,B_1130] : k4_xboole_0(k2_zfmisc_1(A_1128,C_1129),k2_zfmisc_1(B_1130,C_1129)) = k2_zfmisc_1(k4_xboole_0(A_1128,B_1130),C_1129) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_98932,plain,(
    ! [A_1137] : k4_xboole_0(k2_zfmisc_1(A_1137,'#skF_6'),k2_zfmisc_1('#skF_3','#skF_4')) = k2_zfmisc_1(k4_xboole_0(A_1137,'#skF_3'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_98220,c_98826])).

tff(c_98939,plain,(
    k2_zfmisc_1(k4_xboole_0('#skF_3','#skF_3'),'#skF_6') = k2_zfmisc_1('#skF_3',k4_xboole_0('#skF_6','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_98932,c_48])).

tff(c_98970,plain,(
    k2_zfmisc_1('#skF_3',k4_xboole_0('#skF_6','#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_98235,c_98939])).

tff(c_98990,plain,
    ( k4_xboole_0('#skF_6','#skF_4') = k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_98970,c_34])).

tff(c_98999,plain,(
    k4_xboole_0('#skF_6','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_98990])).

tff(c_22,plain,(
    ! [B_16,A_15] :
      ( B_16 = A_15
      | k4_xboole_0(B_16,A_15) != k4_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_99009,plain,
    ( '#skF_6' = '#skF_4'
    | k4_xboole_0('#skF_4','#skF_6') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_98999,c_22])).

tff(c_99022,plain,(
    k4_xboole_0('#skF_4','#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_98105,c_99009])).

tff(c_99549,plain,(
    ! [B_1158] : k4_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1(B_1158,'#skF_6')) = k2_zfmisc_1(k4_xboole_0('#skF_3',B_1158),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_98220,c_98826])).

tff(c_99556,plain,(
    k2_zfmisc_1(k4_xboole_0('#skF_3','#skF_3'),'#skF_6') = k2_zfmisc_1('#skF_3',k4_xboole_0('#skF_4','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_99549,c_48])).

tff(c_99587,plain,(
    k2_zfmisc_1('#skF_3',k4_xboole_0('#skF_4','#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_98235,c_99556])).

tff(c_99617,plain,
    ( k4_xboole_0('#skF_4','#skF_6') = k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_99587,c_34])).

tff(c_99631,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_99022,c_99617])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:55:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 24.64/15.92  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.64/15.94  
% 24.64/15.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.64/15.94  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 24.64/15.94  
% 24.64/15.94  %Foreground sorts:
% 24.64/15.94  
% 24.64/15.94  
% 24.64/15.94  %Background operators:
% 24.64/15.94  
% 24.64/15.94  
% 24.64/15.94  %Foreground operators:
% 24.64/15.94  tff('#skF_2', type, '#skF_2': $i > $i).
% 24.64/15.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 24.64/15.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 24.64/15.94  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 24.64/15.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 24.64/15.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 24.64/15.94  tff('#skF_5', type, '#skF_5': $i).
% 24.64/15.94  tff('#skF_6', type, '#skF_6': $i).
% 24.64/15.94  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 24.64/15.94  tff('#skF_3', type, '#skF_3': $i).
% 24.64/15.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 24.64/15.94  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 24.64/15.94  tff('#skF_4', type, '#skF_4': $i).
% 24.64/15.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 24.64/15.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 24.64/15.94  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 24.64/15.94  
% 24.83/15.97  tff(f_109, negated_conjecture, ~(![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 24.83/15.97  tff(f_98, axiom, (![A, B, C]: ((k2_zfmisc_1(k4_xboole_0(A, B), C) = k4_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k4_xboole_0(A, B)) = k4_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 24.83/15.97  tff(f_59, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 24.83/15.97  tff(f_92, axiom, (![A, B, C]: ~((~(A = k1_xboole_0) & (r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(C, A)) | r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(A, C)))) & ~r1_tarski(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 24.83/15.97  tff(f_81, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 24.83/15.97  tff(f_69, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 24.83/15.97  tff(f_55, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 24.83/15.97  tff(f_71, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 24.83/15.97  tff(f_67, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 24.83/15.97  tff(f_94, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 24.83/15.97  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 24.83/15.97  tff(f_65, axiom, (![A, B]: ((k4_xboole_0(A, B) = k4_xboole_0(B, A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_xboole_1)).
% 24.83/15.97  tff(c_54, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_109])).
% 24.83/15.97  tff(c_52, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_109])).
% 24.83/15.97  tff(c_50, plain, ('#skF_6'!='#skF_4' | '#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_109])).
% 24.83/15.97  tff(c_75, plain, ('#skF_5'!='#skF_3'), inference(splitLeft, [status(thm)], [c_50])).
% 24.83/15.97  tff(c_2561, plain, (![A_162, C_163, B_164]: (k4_xboole_0(k2_zfmisc_1(A_162, C_163), k2_zfmisc_1(B_164, C_163))=k2_zfmisc_1(k4_xboole_0(A_162, B_164), C_163))), inference(cnfTransformation, [status(thm)], [f_98])).
% 24.83/15.97  tff(c_56, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k2_zfmisc_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 24.83/15.97  tff(c_663, plain, (![C_86, A_87, B_88]: (k4_xboole_0(k2_zfmisc_1(C_86, A_87), k2_zfmisc_1(C_86, B_88))=k2_zfmisc_1(C_86, k4_xboole_0(A_87, B_88)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 24.83/15.97  tff(c_695, plain, (![B_88]: (k4_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', B_88))=k2_zfmisc_1('#skF_5', k4_xboole_0('#skF_6', B_88)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_663])).
% 24.83/15.97  tff(c_2581, plain, (k2_zfmisc_1(k4_xboole_0('#skF_3', '#skF_5'), '#skF_4')=k2_zfmisc_1('#skF_5', k4_xboole_0('#skF_6', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2561, c_695])).
% 24.83/15.97  tff(c_46, plain, (![A_33, C_35, B_34]: (k4_xboole_0(k2_zfmisc_1(A_33, C_35), k2_zfmisc_1(B_34, C_35))=k2_zfmisc_1(k4_xboole_0(A_33, B_34), C_35))), inference(cnfTransformation, [status(thm)], [f_98])).
% 24.83/15.97  tff(c_16, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | k4_xboole_0(A_12, B_13)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 24.83/15.97  tff(c_882, plain, (![B_101, A_102, C_103]: (~r1_tarski(k2_zfmisc_1(B_101, A_102), k2_zfmisc_1(C_103, A_102)) | r1_tarski(B_101, C_103) | k1_xboole_0=A_102)), inference(cnfTransformation, [status(thm)], [f_92])).
% 24.83/15.97  tff(c_908, plain, (![B_101, C_103, A_102]: (r1_tarski(B_101, C_103) | k1_xboole_0=A_102 | k4_xboole_0(k2_zfmisc_1(B_101, A_102), k2_zfmisc_1(C_103, A_102))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_882])).
% 24.83/15.97  tff(c_8371, plain, (![B_288, C_289, A_290]: (r1_tarski(B_288, C_289) | k1_xboole_0=A_290 | k2_zfmisc_1(k4_xboole_0(B_288, C_289), A_290)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_908])).
% 24.83/15.97  tff(c_8380, plain, (r1_tarski('#skF_3', '#skF_5') | k1_xboole_0='#skF_4' | k2_zfmisc_1('#skF_5', k4_xboole_0('#skF_6', '#skF_4'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2581, c_8371])).
% 24.83/15.97  tff(c_8449, plain, (r1_tarski('#skF_3', '#skF_5') | k2_zfmisc_1('#skF_5', k4_xboole_0('#skF_6', '#skF_4'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_52, c_8380])).
% 24.83/15.97  tff(c_8467, plain, (k2_zfmisc_1('#skF_5', k4_xboole_0('#skF_6', '#skF_4'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_8449])).
% 24.83/15.97  tff(c_38, plain, (![B_25]: (k2_zfmisc_1(k1_xboole_0, B_25)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_81])).
% 24.83/15.97  tff(c_888, plain, (![C_103]: (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1(C_103, '#skF_6')) | r1_tarski('#skF_5', C_103) | k1_xboole_0='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_56, c_882])).
% 24.83/15.97  tff(c_1900, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_888])).
% 24.83/15.97  tff(c_36, plain, (![A_24]: (k2_zfmisc_1(A_24, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_81])).
% 24.83/15.97  tff(c_1928, plain, (![A_24]: (k2_zfmisc_1(A_24, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1900, c_1900, c_36])).
% 24.83/15.97  tff(c_2318, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1928, c_56])).
% 24.83/15.97  tff(c_333, plain, (![B_62, A_63]: (k1_xboole_0=B_62 | k1_xboole_0=A_63 | k2_zfmisc_1(A_63, B_62)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_81])).
% 24.83/15.97  tff(c_336, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k2_zfmisc_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_56, c_333])).
% 24.83/15.97  tff(c_366, plain, (k2_zfmisc_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_336])).
% 24.83/15.97  tff(c_1916, plain, (k2_zfmisc_1('#skF_3', '#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1900, c_366])).
% 24.83/15.97  tff(c_2466, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2318, c_1916])).
% 24.83/15.97  tff(c_2468, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_888])).
% 24.83/15.97  tff(c_4379, plain, (![A_201]: (k4_xboole_0(k2_zfmisc_1(A_201, '#skF_6'), k2_zfmisc_1('#skF_3', '#skF_4'))=k2_zfmisc_1(k4_xboole_0(A_201, '#skF_5'), '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_2561])).
% 24.83/15.97  tff(c_48, plain, (![C_35, A_33, B_34]: (k4_xboole_0(k2_zfmisc_1(C_35, A_33), k2_zfmisc_1(C_35, B_34))=k2_zfmisc_1(C_35, k4_xboole_0(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 24.83/15.97  tff(c_4416, plain, (k2_zfmisc_1(k4_xboole_0('#skF_3', '#skF_5'), '#skF_6')=k2_zfmisc_1('#skF_3', k4_xboole_0('#skF_6', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4379, c_48])).
% 24.83/15.97  tff(c_8370, plain, (![B_101, C_103, A_102]: (r1_tarski(B_101, C_103) | k1_xboole_0=A_102 | k2_zfmisc_1(k4_xboole_0(B_101, C_103), A_102)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_908])).
% 24.83/15.97  tff(c_9010, plain, (r1_tarski('#skF_3', '#skF_5') | k1_xboole_0='#skF_6' | k2_zfmisc_1('#skF_3', k4_xboole_0('#skF_6', '#skF_4'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4416, c_8370])).
% 24.83/15.97  tff(c_9112, plain, (r1_tarski('#skF_3', '#skF_5') | k2_zfmisc_1('#skF_3', k4_xboole_0('#skF_6', '#skF_4'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_2468, c_9010])).
% 24.83/15.97  tff(c_9127, plain, (k2_zfmisc_1('#skF_3', k4_xboole_0('#skF_6', '#skF_4'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_9112])).
% 24.83/15.97  tff(c_26, plain, (![A_19]: (k4_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_69])).
% 24.83/15.97  tff(c_14, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 24.83/15.97  tff(c_191, plain, (![A_47, B_48]: (k4_xboole_0(A_47, B_48)=k1_xboole_0 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_59])).
% 24.83/15.97  tff(c_199, plain, (![B_11]: (k4_xboole_0(B_11, B_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_191])).
% 24.83/15.97  tff(c_395, plain, (![A_72, B_73]: (k4_xboole_0(A_72, k4_xboole_0(A_72, B_73))=k3_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_71])).
% 24.83/15.97  tff(c_430, plain, (![B_11]: (k4_xboole_0(B_11, k1_xboole_0)=k3_xboole_0(B_11, B_11))), inference(superposition, [status(thm), theory('equality')], [c_199, c_395])).
% 24.83/15.97  tff(c_440, plain, (![B_11]: (k3_xboole_0(B_11, B_11)=B_11)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_430])).
% 24.83/15.97  tff(c_28, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 24.83/15.97  tff(c_24, plain, (![A_17, B_18]: (r1_tarski(k4_xboole_0(A_17, B_18), A_17))), inference(cnfTransformation, [status(thm)], [f_67])).
% 24.83/15.97  tff(c_379, plain, (![B_70, A_71]: (B_70=A_71 | ~r1_tarski(B_70, A_71) | ~r1_tarski(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_55])).
% 24.83/15.97  tff(c_4090, plain, (![B_195, A_196]: (B_195=A_196 | ~r1_tarski(B_195, A_196) | k4_xboole_0(A_196, B_195)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_379])).
% 24.83/15.97  tff(c_4114, plain, (![A_17, B_18]: (k4_xboole_0(A_17, B_18)=A_17 | k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_4090])).
% 24.83/15.97  tff(c_4131, plain, (![A_17, B_18]: (k4_xboole_0(A_17, B_18)=A_17 | k3_xboole_0(A_17, B_18)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_4114])).
% 24.83/15.97  tff(c_44, plain, (![A_29, C_31, B_30, D_32]: (k3_xboole_0(k2_zfmisc_1(A_29, C_31), k2_zfmisc_1(B_30, D_32))=k2_zfmisc_1(k3_xboole_0(A_29, B_30), k3_xboole_0(C_31, D_32)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 24.83/15.97  tff(c_2588, plain, (![A_162, C_163, B_164]: (k4_xboole_0(k2_zfmisc_1(A_162, C_163), k2_zfmisc_1(k4_xboole_0(A_162, B_164), C_163))=k3_xboole_0(k2_zfmisc_1(A_162, C_163), k2_zfmisc_1(B_164, C_163)))), inference(superposition, [status(thm), theory('equality')], [c_2561, c_28])).
% 24.83/15.97  tff(c_11977, plain, (![A_337, C_338, B_339]: (k4_xboole_0(k2_zfmisc_1(A_337, C_338), k2_zfmisc_1(k4_xboole_0(A_337, B_339), C_338))=k2_zfmisc_1(k3_xboole_0(A_337, B_339), C_338))), inference(demodulation, [status(thm), theory('equality')], [c_440, c_44, c_2588])).
% 24.83/15.97  tff(c_12141, plain, (![A_17, C_338, B_18]: (k4_xboole_0(k2_zfmisc_1(A_17, C_338), k2_zfmisc_1(A_17, C_338))=k2_zfmisc_1(k3_xboole_0(A_17, B_18), C_338) | k3_xboole_0(A_17, B_18)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4131, c_11977])).
% 24.83/15.97  tff(c_12270, plain, (![A_340, B_341, C_342]: (k2_zfmisc_1(k3_xboole_0(A_340, B_341), C_342)=k1_xboole_0 | k3_xboole_0(A_340, B_341)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_199, c_48, c_12141])).
% 24.83/15.97  tff(c_12489, plain, (![B_11, C_342]: (k2_zfmisc_1(B_11, C_342)=k1_xboole_0 | k3_xboole_0(B_11, B_11)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_440, c_12270])).
% 24.83/15.97  tff(c_12568, plain, (![B_343, C_344]: (k2_zfmisc_1(B_343, C_344)=k1_xboole_0 | k1_xboole_0!=B_343)), inference(demodulation, [status(thm), theory('equality')], [c_440, c_12489])).
% 24.83/15.97  tff(c_12642, plain, (k2_zfmisc_1('#skF_3', k4_xboole_0('#skF_6', '#skF_4'))=k1_xboole_0 | k4_xboole_0('#skF_3', '#skF_5')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_12568, c_4416])).
% 24.83/15.97  tff(c_12944, plain, (k4_xboole_0('#skF_3', '#skF_5')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_9127, c_12642])).
% 24.83/15.97  tff(c_11976, plain, (![A_162, C_163, B_164]: (k4_xboole_0(k2_zfmisc_1(A_162, C_163), k2_zfmisc_1(k4_xboole_0(A_162, B_164), C_163))=k2_zfmisc_1(k3_xboole_0(A_162, B_164), C_163))), inference(demodulation, [status(thm), theory('equality')], [c_440, c_44, c_2588])).
% 24.83/15.97  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 24.83/15.97  tff(c_4419, plain, (![A_201]: (k4_xboole_0(k2_zfmisc_1(A_201, '#skF_6'), k2_zfmisc_1(k4_xboole_0(A_201, '#skF_5'), '#skF_6'))=k3_xboole_0(k2_zfmisc_1(A_201, '#skF_6'), k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_4379, c_28])).
% 24.83/15.97  tff(c_4466, plain, (![A_201]: (k4_xboole_0(k2_zfmisc_1(A_201, '#skF_6'), k2_zfmisc_1(k4_xboole_0(A_201, '#skF_5'), '#skF_6'))=k2_zfmisc_1(k3_xboole_0(A_201, '#skF_3'), k3_xboole_0('#skF_4', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_44, c_4419])).
% 24.83/15.97  tff(c_52444, plain, (![A_678]: (k2_zfmisc_1(k3_xboole_0(A_678, '#skF_3'), k3_xboole_0('#skF_4', '#skF_6'))=k2_zfmisc_1(k3_xboole_0(A_678, '#skF_5'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_11976, c_4466])).
% 24.83/15.97  tff(c_3334, plain, (![A_178, C_179, B_180, D_181]: (k3_xboole_0(k2_zfmisc_1(A_178, C_179), k2_zfmisc_1(B_180, D_181))=k2_zfmisc_1(k3_xboole_0(A_178, B_180), k3_xboole_0(C_179, D_181)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 24.83/15.97  tff(c_411, plain, (![A_72, B_73]: (r1_tarski(k3_xboole_0(A_72, B_73), A_72))), inference(superposition, [status(thm), theory('equality')], [c_395, c_24])).
% 24.83/15.97  tff(c_3376, plain, (![A_178, B_180, C_179, D_181]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_178, B_180), k3_xboole_0(C_179, D_181)), k2_zfmisc_1(A_178, C_179)))), inference(superposition, [status(thm), theory('equality')], [c_3334, c_411])).
% 24.83/15.97  tff(c_68140, plain, (![A_795]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_795, '#skF_5'), '#skF_6'), k2_zfmisc_1(A_795, '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_52444, c_3376])).
% 24.83/15.97  tff(c_68291, plain, (r1_tarski(k2_zfmisc_1('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_5', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_440, c_68140])).
% 24.83/15.97  tff(c_68334, plain, (r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_68291])).
% 24.83/15.97  tff(c_42, plain, (![B_27, A_26, C_28]: (~r1_tarski(k2_zfmisc_1(B_27, A_26), k2_zfmisc_1(C_28, A_26)) | r1_tarski(B_27, C_28) | k1_xboole_0=A_26)), inference(cnfTransformation, [status(thm)], [f_92])).
% 24.83/15.97  tff(c_68349, plain, (r1_tarski('#skF_3', '#skF_5') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_68334, c_42])).
% 24.83/15.97  tff(c_68375, plain, (r1_tarski('#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_52, c_68349])).
% 24.83/15.97  tff(c_18, plain, (![A_12, B_13]: (k4_xboole_0(A_12, B_13)=k1_xboole_0 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 24.83/15.97  tff(c_68395, plain, (k4_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_68375, c_18])).
% 24.83/15.97  tff(c_68409, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12944, c_68395])).
% 24.83/15.97  tff(c_68410, plain, (r1_tarski('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_9112])).
% 24.83/15.97  tff(c_68432, plain, (k4_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_68410, c_18])).
% 24.83/15.97  tff(c_68444, plain, (k2_zfmisc_1('#skF_5', k4_xboole_0('#skF_6', '#skF_4'))=k2_zfmisc_1(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68432, c_2581])).
% 24.83/15.97  tff(c_68446, plain, (k2_zfmisc_1('#skF_5', k4_xboole_0('#skF_6', '#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_68444])).
% 24.83/15.97  tff(c_68448, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8467, c_68446])).
% 24.83/15.97  tff(c_68449, plain, (r1_tarski('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_8449])).
% 24.83/15.97  tff(c_10, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 24.83/15.97  tff(c_68458, plain, ('#skF_5'='#skF_3' | ~r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_68449, c_10])).
% 24.83/15.97  tff(c_68470, plain, (~r1_tarski('#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_75, c_68458])).
% 24.83/15.97  tff(c_68471, plain, (k4_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_68449, c_18])).
% 24.83/15.97  tff(c_198, plain, (![A_17, B_18]: (k4_xboole_0(k4_xboole_0(A_17, B_18), A_17)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_191])).
% 24.83/15.97  tff(c_420, plain, (![A_17, B_18]: (k4_xboole_0(k4_xboole_0(A_17, B_18), k1_xboole_0)=k3_xboole_0(k4_xboole_0(A_17, B_18), A_17))), inference(superposition, [status(thm), theory('equality')], [c_198, c_395])).
% 24.83/15.97  tff(c_1071, plain, (![A_115, B_116]: (k3_xboole_0(k4_xboole_0(A_115, B_116), A_115)=k4_xboole_0(A_115, B_116))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_420])).
% 24.83/15.97  tff(c_1143, plain, (![A_1, B_116]: (k3_xboole_0(A_1, k4_xboole_0(A_1, B_116))=k4_xboole_0(A_1, B_116))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1071])).
% 24.83/15.97  tff(c_4136, plain, (![A_197, B_198]: (k4_xboole_0(A_197, B_198)=A_197 | k3_xboole_0(A_197, B_198)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_4114])).
% 24.83/15.97  tff(c_4196, plain, (![A_197, B_21]: (k3_xboole_0(A_197, B_21)=A_197 | k3_xboole_0(A_197, k4_xboole_0(A_197, B_21))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4136, c_28])).
% 24.83/15.97  tff(c_4286, plain, (![A_197, B_21]: (k3_xboole_0(A_197, B_21)=A_197 | k4_xboole_0(A_197, B_21)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1143, c_4196])).
% 24.83/15.97  tff(c_68572, plain, (k3_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_68471, c_4286])).
% 24.83/15.97  tff(c_70666, plain, (![A_162, C_163, B_164]: (k4_xboole_0(k2_zfmisc_1(A_162, C_163), k2_zfmisc_1(k4_xboole_0(A_162, B_164), C_163))=k2_zfmisc_1(k3_xboole_0(A_162, B_164), C_163))), inference(demodulation, [status(thm), theory('equality')], [c_440, c_44, c_2588])).
% 24.83/15.97  tff(c_1190, plain, (![A_118, B_119, C_120]: (~r1_tarski(k2_zfmisc_1(A_118, B_119), k2_zfmisc_1(A_118, C_120)) | r1_tarski(B_119, C_120) | k1_xboole_0=A_118)), inference(cnfTransformation, [status(thm)], [f_92])).
% 24.83/15.97  tff(c_1196, plain, (![C_120]: (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', C_120)) | r1_tarski('#skF_6', C_120) | k1_xboole_0='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_56, c_1190])).
% 24.83/15.97  tff(c_1336, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_1196])).
% 24.83/15.97  tff(c_1362, plain, (![B_25]: (k2_zfmisc_1('#skF_5', B_25)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1336, c_1336, c_38])).
% 24.83/15.97  tff(c_1697, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1362, c_56])).
% 24.83/15.97  tff(c_1351, plain, (k2_zfmisc_1('#skF_3', '#skF_4')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1336, c_366])).
% 24.83/15.97  tff(c_1897, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1697, c_1351])).
% 24.83/15.97  tff(c_1899, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_1196])).
% 24.83/15.97  tff(c_68450, plain, (k2_zfmisc_1('#skF_5', k4_xboole_0('#skF_6', '#skF_4'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_8449])).
% 24.83/15.97  tff(c_34, plain, (![B_25, A_24]: (k1_xboole_0=B_25 | k1_xboole_0=A_24 | k2_zfmisc_1(A_24, B_25)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_81])).
% 24.83/15.97  tff(c_69538, plain, (k4_xboole_0('#skF_6', '#skF_4')=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_68450, c_34])).
% 24.83/15.97  tff(c_69586, plain, (k4_xboole_0('#skF_6', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_1899, c_69538])).
% 24.83/15.97  tff(c_414, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k3_xboole_0(A_20, B_21))=k3_xboole_0(A_20, k4_xboole_0(A_20, B_21)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_395])).
% 24.83/15.97  tff(c_6289, plain, (![A_246, B_247]: (k4_xboole_0(A_246, k3_xboole_0(A_246, B_247))=k4_xboole_0(A_246, B_247))), inference(demodulation, [status(thm), theory('equality')], [c_1143, c_414])).
% 24.83/15.97  tff(c_6409, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_6289])).
% 24.83/15.97  tff(c_474, plain, (![A_75, B_76]: (r1_tarski(k3_xboole_0(A_75, B_76), A_75))), inference(superposition, [status(thm), theory('equality')], [c_395, c_24])).
% 24.83/15.97  tff(c_500, plain, (![B_77, A_78]: (r1_tarski(k3_xboole_0(B_77, A_78), A_78))), inference(superposition, [status(thm), theory('equality')], [c_2, c_474])).
% 24.83/15.97  tff(c_6694, plain, (![B_251, A_252]: (k3_xboole_0(B_251, A_252)=A_252 | ~r1_tarski(A_252, k3_xboole_0(B_251, A_252)))), inference(resolution, [status(thm)], [c_500, c_10])).
% 24.83/15.97  tff(c_6734, plain, (![B_251, A_12]: (k3_xboole_0(B_251, A_12)=A_12 | k4_xboole_0(A_12, k3_xboole_0(B_251, A_12))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_6694])).
% 24.83/15.97  tff(c_6770, plain, (![B_251, A_12]: (k3_xboole_0(B_251, A_12)=A_12 | k4_xboole_0(A_12, B_251)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6409, c_6734])).
% 24.83/15.97  tff(c_69701, plain, (k3_xboole_0('#skF_4', '#skF_6')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_69586, c_6770])).
% 24.83/15.97  tff(c_97615, plain, (![A_1074]: (k2_zfmisc_1(k3_xboole_0(A_1074, '#skF_5'), '#skF_6')=k2_zfmisc_1(k3_xboole_0(A_1074, '#skF_3'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_70666, c_69701, c_4466])).
% 24.83/15.97  tff(c_97849, plain, (k2_zfmisc_1(k3_xboole_0('#skF_5', '#skF_3'), '#skF_6')=k2_zfmisc_1('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_440, c_97615])).
% 24.83/15.97  tff(c_97913, plain, (k2_zfmisc_1('#skF_3', '#skF_6')=k2_zfmisc_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68572, c_56, c_2, c_97849])).
% 24.83/15.97  tff(c_2467, plain, (![C_103]: (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1(C_103, '#skF_6')) | r1_tarski('#skF_5', C_103))), inference(splitRight, [status(thm)], [c_888])).
% 24.83/15.97  tff(c_97995, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_3', '#skF_4')) | r1_tarski('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_97913, c_2467])).
% 24.83/15.97  tff(c_98081, plain, (r1_tarski('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_97995])).
% 24.83/15.97  tff(c_98083, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68470, c_98081])).
% 24.83/15.97  tff(c_98085, plain, (k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_336])).
% 24.83/15.97  tff(c_98098, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_98085, c_34])).
% 24.83/15.97  tff(c_98104, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_52, c_98098])).
% 24.83/15.97  tff(c_98105, plain, ('#skF_6'!='#skF_4'), inference(splitRight, [status(thm)], [c_50])).
% 24.83/15.97  tff(c_98227, plain, (![A_1084, B_1085]: (k4_xboole_0(A_1084, B_1085)=k1_xboole_0 | ~r1_tarski(A_1084, B_1085))), inference(cnfTransformation, [status(thm)], [f_59])).
% 24.83/15.97  tff(c_98235, plain, (![B_11]: (k4_xboole_0(B_11, B_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_98227])).
% 24.83/15.97  tff(c_98106, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_50])).
% 24.83/15.97  tff(c_98220, plain, (k2_zfmisc_1('#skF_3', '#skF_6')=k2_zfmisc_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_98106, c_56])).
% 24.83/15.97  tff(c_98826, plain, (![A_1128, C_1129, B_1130]: (k4_xboole_0(k2_zfmisc_1(A_1128, C_1129), k2_zfmisc_1(B_1130, C_1129))=k2_zfmisc_1(k4_xboole_0(A_1128, B_1130), C_1129))), inference(cnfTransformation, [status(thm)], [f_98])).
% 24.83/15.97  tff(c_98932, plain, (![A_1137]: (k4_xboole_0(k2_zfmisc_1(A_1137, '#skF_6'), k2_zfmisc_1('#skF_3', '#skF_4'))=k2_zfmisc_1(k4_xboole_0(A_1137, '#skF_3'), '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_98220, c_98826])).
% 24.83/15.97  tff(c_98939, plain, (k2_zfmisc_1(k4_xboole_0('#skF_3', '#skF_3'), '#skF_6')=k2_zfmisc_1('#skF_3', k4_xboole_0('#skF_6', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_98932, c_48])).
% 24.83/15.97  tff(c_98970, plain, (k2_zfmisc_1('#skF_3', k4_xboole_0('#skF_6', '#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_98235, c_98939])).
% 24.83/15.97  tff(c_98990, plain, (k4_xboole_0('#skF_6', '#skF_4')=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_98970, c_34])).
% 24.83/15.97  tff(c_98999, plain, (k4_xboole_0('#skF_6', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_54, c_98990])).
% 24.83/15.97  tff(c_22, plain, (![B_16, A_15]: (B_16=A_15 | k4_xboole_0(B_16, A_15)!=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 24.83/15.97  tff(c_99009, plain, ('#skF_6'='#skF_4' | k4_xboole_0('#skF_4', '#skF_6')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_98999, c_22])).
% 24.83/15.97  tff(c_99022, plain, (k4_xboole_0('#skF_4', '#skF_6')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_98105, c_99009])).
% 24.83/15.97  tff(c_99549, plain, (![B_1158]: (k4_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1(B_1158, '#skF_6'))=k2_zfmisc_1(k4_xboole_0('#skF_3', B_1158), '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_98220, c_98826])).
% 24.83/15.97  tff(c_99556, plain, (k2_zfmisc_1(k4_xboole_0('#skF_3', '#skF_3'), '#skF_6')=k2_zfmisc_1('#skF_3', k4_xboole_0('#skF_4', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_99549, c_48])).
% 24.83/15.97  tff(c_99587, plain, (k2_zfmisc_1('#skF_3', k4_xboole_0('#skF_4', '#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_98235, c_99556])).
% 24.83/15.97  tff(c_99617, plain, (k4_xboole_0('#skF_4', '#skF_6')=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_99587, c_34])).
% 24.83/15.97  tff(c_99631, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_99022, c_99617])).
% 24.83/15.97  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.83/15.97  
% 24.83/15.97  Inference rules
% 24.83/15.97  ----------------------
% 24.83/15.97  #Ref     : 17
% 24.83/15.97  #Sup     : 25177
% 24.83/15.97  #Fact    : 0
% 24.83/15.97  #Define  : 0
% 24.83/15.97  #Split   : 30
% 24.83/15.97  #Chain   : 0
% 24.83/15.97  #Close   : 0
% 24.83/15.97  
% 24.83/15.97  Ordering : KBO
% 24.83/15.97  
% 24.83/15.97  Simplification rules
% 24.83/15.97  ----------------------
% 24.83/15.97  #Subsume      : 6662
% 24.83/15.97  #Demod        : 22374
% 24.83/15.97  #Tautology    : 8978
% 24.83/15.97  #SimpNegUnit  : 531
% 24.83/15.97  #BackRed      : 115
% 24.83/15.97  
% 24.83/15.97  #Partial instantiations: 0
% 24.83/15.97  #Strategies tried      : 1
% 24.83/15.97  
% 24.83/15.97  Timing (in seconds)
% 24.83/15.97  ----------------------
% 24.83/15.97  Preprocessing        : 0.33
% 24.83/15.97  Parsing              : 0.17
% 24.83/15.97  CNF conversion       : 0.02
% 24.83/15.97  Main loop            : 14.83
% 24.83/15.97  Inferencing          : 1.77
% 24.83/15.97  Reduction            : 8.54
% 24.83/15.97  Demodulation         : 7.45
% 24.83/15.97  BG Simplification    : 0.22
% 24.83/15.97  Subsumption          : 3.48
% 24.83/15.97  Abstraction          : 0.36
% 24.83/15.97  MUC search           : 0.00
% 24.83/15.97  Cooper               : 0.00
% 24.83/15.97  Total                : 15.22
% 24.83/15.97  Index Insertion      : 0.00
% 24.83/15.97  Index Deletion       : 0.00
% 24.83/15.97  Index Matching       : 0.00
% 24.83/15.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
