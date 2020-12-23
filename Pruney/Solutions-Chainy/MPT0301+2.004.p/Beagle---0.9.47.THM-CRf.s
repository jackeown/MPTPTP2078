%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:40 EST 2020

% Result     : Theorem 6.21s
% Output     : CNFRefutation 6.47s
% Verified   : 
% Statistics : Number of formulae       :  180 (1660 expanded)
%              Number of leaves         :   28 ( 494 expanded)
%              Depth                    :   12
%              Number of atoms          :  228 (3173 expanded)
%              Number of equality atoms :  116 (2729 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k5_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_45,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_43,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_9816,plain,(
    ! [A_928,B_929,C_930] :
      ( r2_hidden('#skF_4'(A_928,B_929,C_930),B_929)
      | r2_hidden('#skF_5'(A_928,B_929,C_930),C_930)
      | k2_zfmisc_1(A_928,B_929) = C_930 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8690,plain,(
    ! [A_835,B_836,C_837] :
      ( r2_hidden('#skF_4'(A_835,B_836,C_837),B_836)
      | r2_hidden('#skF_5'(A_835,B_836,C_837),C_837)
      | k2_zfmisc_1(A_835,B_836) = C_837 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6926,plain,(
    ! [A_681,B_682,C_683] :
      ( r2_hidden('#skF_4'(A_681,B_682,C_683),B_682)
      | r2_hidden('#skF_5'(A_681,B_682,C_683),C_683)
      | k2_zfmisc_1(A_681,B_682) = C_683 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2467,plain,(
    ! [A_289,B_290,C_291] :
      ( r2_hidden('#skF_4'(A_289,B_290,C_291),B_290)
      | r2_hidden('#skF_5'(A_289,B_290,C_291),C_291)
      | k2_zfmisc_1(A_289,B_290) = C_291 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_40,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_1430,plain,(
    ! [A_198,B_199,C_200] :
      ( r2_hidden('#skF_4'(A_198,B_199,C_200),B_199)
      | r2_hidden('#skF_5'(A_198,B_199,C_200),C_200)
      | k2_zfmisc_1(A_198,B_199) = C_200 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_42,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0
    | k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_65,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_651,plain,(
    ! [A_129,B_130,C_131] :
      ( r2_hidden('#skF_4'(A_129,B_130,C_131),B_130)
      | r2_hidden('#skF_5'(A_129,B_130,C_131),C_131)
      | k2_zfmisc_1(A_129,B_130) = C_131 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_150,plain,(
    ! [A_51,B_52] : r1_xboole_0(k3_xboole_0(A_51,B_52),k5_xboole_0(A_51,B_52)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_162,plain,(
    ! [A_10] : r1_xboole_0(k1_xboole_0,k5_xboole_0(A_10,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_150])).

tff(c_166,plain,(
    ! [A_10] : r1_xboole_0(k1_xboole_0,A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_162])).

tff(c_67,plain,(
    ! [B_48,A_49] : k3_xboole_0(B_48,A_49) = k3_xboole_0(A_49,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_83,plain,(
    ! [A_49] : k3_xboole_0(k1_xboole_0,A_49) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_10])).

tff(c_199,plain,(
    ! [A_56,B_57,C_58] :
      ( ~ r1_xboole_0(A_56,B_57)
      | ~ r2_hidden(C_58,k3_xboole_0(A_56,B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_202,plain,(
    ! [A_49,C_58] :
      ( ~ r1_xboole_0(k1_xboole_0,A_49)
      | ~ r2_hidden(C_58,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_199])).

tff(c_213,plain,(
    ! [C_58] : ~ r2_hidden(C_58,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_202])).

tff(c_48,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k2_zfmisc_1('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_169,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_272,plain,(
    ! [E_68,F_69,A_70,B_71] :
      ( r2_hidden(k4_tarski(E_68,F_69),k2_zfmisc_1(A_70,B_71))
      | ~ r2_hidden(F_69,B_71)
      | ~ r2_hidden(E_68,A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_275,plain,(
    ! [E_68,F_69] :
      ( r2_hidden(k4_tarski(E_68,F_69),k1_xboole_0)
      | ~ r2_hidden(F_69,'#skF_11')
      | ~ r2_hidden(E_68,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_272])).

tff(c_276,plain,(
    ! [F_69,E_68] :
      ( ~ r2_hidden(F_69,'#skF_11')
      | ~ r2_hidden(E_68,'#skF_10') ) ),
    inference(negUnitSimplification,[status(thm)],[c_213,c_275])).

tff(c_277,plain,(
    ! [E_68] : ~ r2_hidden(E_68,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_276])).

tff(c_916,plain,(
    ! [A_144,C_145] :
      ( r2_hidden('#skF_5'(A_144,'#skF_10',C_145),C_145)
      | k2_zfmisc_1(A_144,'#skF_10') = C_145 ) ),
    inference(resolution,[status(thm)],[c_651,c_277])).

tff(c_1023,plain,(
    ! [A_144] : k2_zfmisc_1(A_144,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_916,c_277])).

tff(c_1025,plain,(
    ! [A_144] : k2_zfmisc_1(A_144,'#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_916,c_213])).

tff(c_1091,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1023,c_1025])).

tff(c_1092,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_1091])).

tff(c_1093,plain,(
    ! [F_69] : ~ r2_hidden(F_69,'#skF_11') ),
    inference(splitRight,[status(thm)],[c_276])).

tff(c_1687,plain,(
    ! [A_213,C_214] :
      ( r2_hidden('#skF_5'(A_213,'#skF_11',C_214),C_214)
      | k2_zfmisc_1(A_213,'#skF_11') = C_214 ) ),
    inference(resolution,[status(thm)],[c_1430,c_1093])).

tff(c_1789,plain,(
    ! [A_213] : k2_zfmisc_1(A_213,'#skF_11') = '#skF_11' ),
    inference(resolution,[status(thm)],[c_1687,c_1093])).

tff(c_1801,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1789,c_169])).

tff(c_1803,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1801])).

tff(c_1804,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1807,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_1804])).

tff(c_1808,plain,(
    ! [A_10] : r1_xboole_0('#skF_9',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1807,c_166])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1831,plain,(
    ! [A_217] : k3_xboole_0(A_217,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1807,c_1807,c_10])).

tff(c_1852,plain,(
    ! [B_2] : k3_xboole_0('#skF_9',B_2) = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1831])).

tff(c_1898,plain,(
    ! [A_219,B_220,C_221] :
      ( ~ r1_xboole_0(A_219,B_220)
      | ~ r2_hidden(C_221,k3_xboole_0(A_219,B_220)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1901,plain,(
    ! [B_2,C_221] :
      ( ~ r1_xboole_0('#skF_9',B_2)
      | ~ r2_hidden(C_221,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1852,c_1898])).

tff(c_1912,plain,(
    ! [C_221] : ~ r2_hidden(C_221,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1808,c_1901])).

tff(c_3551,plain,(
    ! [A_362,C_363] :
      ( r2_hidden('#skF_5'(A_362,'#skF_9',C_363),C_363)
      | k2_zfmisc_1(A_362,'#skF_9') = C_363 ) ),
    inference(resolution,[status(thm)],[c_2467,c_1912])).

tff(c_3600,plain,(
    ! [A_362] : k2_zfmisc_1(A_362,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_3551,c_1912])).

tff(c_46,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0
    | k2_zfmisc_1('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1856,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != '#skF_9'
    | k2_zfmisc_1('#skF_10','#skF_11') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1807,c_1807,c_46])).

tff(c_1857,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_1856])).

tff(c_3612,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3600,c_1857])).

tff(c_3613,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1856])).

tff(c_1805,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_3624,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3613,c_1807,c_1805])).

tff(c_3625,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1804])).

tff(c_4936,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3625,c_1805])).

tff(c_4138,plain,(
    ! [A_423,B_424,C_425] :
      ( r2_hidden('#skF_3'(A_423,B_424,C_425),A_423)
      | r2_hidden('#skF_5'(A_423,B_424,C_425),C_425)
      | k2_zfmisc_1(A_423,B_424) = C_425 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_3627,plain,(
    ! [A_10] : r1_xboole_0('#skF_8',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3625,c_166])).

tff(c_3628,plain,(
    ! [A_49] : k3_xboole_0('#skF_8',A_49) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3625,c_3625,c_83])).

tff(c_3718,plain,(
    ! [A_368,B_369,C_370] :
      ( ~ r1_xboole_0(A_368,B_369)
      | ~ r2_hidden(C_370,k3_xboole_0(A_368,B_369)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3721,plain,(
    ! [A_49,C_370] :
      ( ~ r1_xboole_0('#skF_8',A_49)
      | ~ r2_hidden(C_370,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3628,c_3718])).

tff(c_3732,plain,(
    ! [C_370] : ~ r2_hidden(C_370,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3627,c_3721])).

tff(c_4817,plain,(
    ! [A_484,B_485] :
      ( r2_hidden('#skF_3'(A_484,B_485,'#skF_8'),A_484)
      | k2_zfmisc_1(A_484,B_485) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_4138,c_3732])).

tff(c_4921,plain,(
    ! [B_485] : k2_zfmisc_1('#skF_8',B_485) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_4817,c_3732])).

tff(c_3638,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != '#skF_8'
    | k2_zfmisc_1('#skF_10','#skF_11') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3625,c_3625,c_46])).

tff(c_3639,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_3638])).

tff(c_4932,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4921,c_3639])).

tff(c_4933,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_3638])).

tff(c_4953,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4936,c_4933])).

tff(c_4955,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_4954,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_4965,plain,
    ( '#skF_11' = '#skF_8'
    | '#skF_11' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4955,c_4955,c_4954])).

tff(c_4966,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_4965])).

tff(c_4958,plain,(
    ! [A_11] : k5_xboole_0(A_11,'#skF_11') = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4955,c_12])).

tff(c_4978,plain,(
    ! [A_11] : k5_xboole_0(A_11,'#skF_9') = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4966,c_4958])).

tff(c_4957,plain,(
    ! [A_10] : k3_xboole_0(A_10,'#skF_11') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4955,c_4955,c_10])).

tff(c_4988,plain,(
    ! [A_10] : k3_xboole_0(A_10,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4966,c_4966,c_4957])).

tff(c_5080,plain,(
    ! [A_493,B_494] : r1_xboole_0(k3_xboole_0(A_493,B_494),k5_xboole_0(A_493,B_494)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5092,plain,(
    ! [A_10] : r1_xboole_0('#skF_9',k5_xboole_0(A_10,'#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4988,c_5080])).

tff(c_5096,plain,(
    ! [A_10] : r1_xboole_0('#skF_9',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4978,c_5092])).

tff(c_5831,plain,(
    ! [A_584,B_585,C_586] :
      ( r2_hidden('#skF_4'(A_584,B_585,C_586),B_585)
      | r2_hidden('#skF_5'(A_584,B_585,C_586),C_586)
      | k2_zfmisc_1(A_584,B_585) = C_586 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_5098,plain,(
    ! [A_495,B_496,C_497] :
      ( ~ r1_xboole_0(A_495,B_496)
      | ~ r2_hidden(C_497,k3_xboole_0(A_495,B_496)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5110,plain,(
    ! [A_10,C_497] :
      ( ~ r1_xboole_0(A_10,'#skF_9')
      | ~ r2_hidden(C_497,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4988,c_5098])).

tff(c_5115,plain,(
    ! [C_497] : ~ r2_hidden(C_497,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_5110])).

tff(c_6195,plain,(
    ! [A_607,C_608] :
      ( r2_hidden('#skF_5'(A_607,'#skF_9',C_608),C_608)
      | k2_zfmisc_1(A_607,'#skF_9') = C_608 ) ),
    inference(resolution,[status(thm)],[c_5831,c_5115])).

tff(c_6299,plain,(
    ! [A_607] : k2_zfmisc_1(A_607,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_6195,c_5115])).

tff(c_38,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4964,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4955,c_4955,c_38])).

tff(c_4968,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4966,c_4964])).

tff(c_6311,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6299,c_4968])).

tff(c_6313,plain,(
    ! [A_609] : ~ r1_xboole_0(A_609,'#skF_9') ),
    inference(splitRight,[status(thm)],[c_5110])).

tff(c_6318,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_5096,c_6313])).

tff(c_6319,plain,(
    '#skF_11' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_4965])).

tff(c_6334,plain,(
    ! [A_11] : k5_xboole_0(A_11,'#skF_8') = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6319,c_4958])).

tff(c_6344,plain,(
    ! [A_10] : k3_xboole_0(A_10,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6319,c_6319,c_4957])).

tff(c_6437,plain,(
    ! [A_615,B_616] : r1_xboole_0(k3_xboole_0(A_615,B_616),k5_xboole_0(A_615,B_616)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6449,plain,(
    ! [A_10] : r1_xboole_0('#skF_8',k5_xboole_0(A_10,'#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6344,c_6437])).

tff(c_6453,plain,(
    ! [A_10] : r1_xboole_0('#skF_8',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6334,c_6449])).

tff(c_6352,plain,(
    ! [B_612,A_613] : k3_xboole_0(B_612,A_613) = k3_xboole_0(A_613,B_612) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6368,plain,(
    ! [A_613] : k3_xboole_0('#skF_8',A_613) = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_6352,c_6344])).

tff(c_6456,plain,(
    ! [A_618,B_619,C_620] :
      ( ~ r1_xboole_0(A_618,B_619)
      | ~ r2_hidden(C_620,k3_xboole_0(A_618,B_619)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6459,plain,(
    ! [A_613,C_620] :
      ( ~ r1_xboole_0('#skF_8',A_613)
      | ~ r2_hidden(C_620,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6368,c_6456])).

tff(c_6470,plain,(
    ! [C_620] : ~ r2_hidden(C_620,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6453,c_6459])).

tff(c_7561,plain,(
    ! [A_727,C_728] :
      ( r2_hidden('#skF_5'(A_727,'#skF_8',C_728),C_728)
      | k2_zfmisc_1(A_727,'#skF_8') = C_728 ) ),
    inference(resolution,[status(thm)],[c_6926,c_6470])).

tff(c_7665,plain,(
    ! [A_727] : k2_zfmisc_1(A_727,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_7561,c_6470])).

tff(c_6644,plain,(
    ! [A_648,B_649,D_650] :
      ( r2_hidden('#skF_6'(A_648,B_649,k2_zfmisc_1(A_648,B_649),D_650),A_648)
      | ~ r2_hidden(D_650,k2_zfmisc_1(A_648,B_649)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6668,plain,(
    ! [D_650,B_649] : ~ r2_hidden(D_650,k2_zfmisc_1('#skF_8',B_649)) ),
    inference(resolution,[status(thm)],[c_6644,c_6470])).

tff(c_7661,plain,(
    ! [A_727,B_649] : k2_zfmisc_1(A_727,'#skF_8') = k2_zfmisc_1('#skF_8',B_649) ),
    inference(resolution,[status(thm)],[c_7561,c_6668])).

tff(c_7754,plain,(
    ! [B_649] : k2_zfmisc_1('#skF_8',B_649) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7665,c_7661])).

tff(c_6323,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6319,c_4964])).

tff(c_7768,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7754,c_6323])).

tff(c_7770,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_44,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_7779,plain,
    ( '#skF_10' = '#skF_9'
    | '#skF_10' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7770,c_7770,c_7770,c_44])).

tff(c_7780,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_7779])).

tff(c_7772,plain,(
    ! [A_11] : k5_xboole_0(A_11,'#skF_10') = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7770,c_12])).

tff(c_7791,plain,(
    ! [A_11] : k5_xboole_0(A_11,'#skF_8') = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7780,c_7772])).

tff(c_7771,plain,(
    ! [A_10] : k3_xboole_0(A_10,'#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7770,c_7770,c_10])).

tff(c_7801,plain,(
    ! [A_10] : k3_xboole_0(A_10,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7780,c_7780,c_7771])).

tff(c_7894,plain,(
    ! [A_740,B_741] : r1_xboole_0(k3_xboole_0(A_740,B_741),k5_xboole_0(A_740,B_741)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_7906,plain,(
    ! [A_10] : r1_xboole_0('#skF_8',k5_xboole_0(A_10,'#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7801,c_7894])).

tff(c_7910,plain,(
    ! [A_10] : r1_xboole_0('#skF_8',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7791,c_7906])).

tff(c_7810,plain,(
    ! [B_737,A_738] : k3_xboole_0(B_737,A_738) = k3_xboole_0(A_738,B_737) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_7826,plain,(
    ! [A_738] : k3_xboole_0('#skF_8',A_738) = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_7810,c_7801])).

tff(c_7914,plain,(
    ! [A_743,B_744,C_745] :
      ( ~ r1_xboole_0(A_743,B_744)
      | ~ r2_hidden(C_745,k3_xboole_0(A_743,B_744)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_7917,plain,(
    ! [A_738,C_745] :
      ( ~ r1_xboole_0('#skF_8',A_738)
      | ~ r2_hidden(C_745,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7826,c_7914])).

tff(c_7928,plain,(
    ! [C_745] : ~ r2_hidden(C_745,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7910,c_7917])).

tff(c_9004,plain,(
    ! [A_849,C_850] :
      ( r2_hidden('#skF_5'(A_849,'#skF_8',C_850),C_850)
      | k2_zfmisc_1(A_849,'#skF_8') = C_850 ) ),
    inference(resolution,[status(thm)],[c_8690,c_7928])).

tff(c_9108,plain,(
    ! [A_849] : k2_zfmisc_1(A_849,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_9004,c_7928])).

tff(c_8135,plain,(
    ! [A_779,B_780,D_781] :
      ( r2_hidden('#skF_6'(A_779,B_780,k2_zfmisc_1(A_779,B_780),D_781),A_779)
      | ~ r2_hidden(D_781,k2_zfmisc_1(A_779,B_780)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8164,plain,(
    ! [D_781,B_780] : ~ r2_hidden(D_781,k2_zfmisc_1('#skF_8',B_780)) ),
    inference(resolution,[status(thm)],[c_8135,c_7928])).

tff(c_9103,plain,(
    ! [A_849,B_780] : k2_zfmisc_1(A_849,'#skF_8') = k2_zfmisc_1('#skF_8',B_780) ),
    inference(resolution,[status(thm)],[c_9004,c_8164])).

tff(c_9195,plain,(
    ! [B_780] : k2_zfmisc_1('#skF_8',B_780) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9108,c_9103])).

tff(c_7769,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_7777,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7770,c_7769])).

tff(c_7781,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7780,c_7777])).

tff(c_9209,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9195,c_7781])).

tff(c_9210,plain,(
    '#skF_10' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_7779])).

tff(c_9225,plain,(
    ! [A_11] : k5_xboole_0(A_11,'#skF_9') = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9210,c_7772])).

tff(c_9235,plain,(
    ! [A_10] : k3_xboole_0(A_10,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9210,c_9210,c_7771])).

tff(c_9329,plain,(
    ! [A_862,B_863] : r1_xboole_0(k3_xboole_0(A_862,B_863),k5_xboole_0(A_862,B_863)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_9341,plain,(
    ! [A_10] : r1_xboole_0('#skF_9',k5_xboole_0(A_10,'#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9235,c_9329])).

tff(c_9345,plain,(
    ! [A_10] : r1_xboole_0('#skF_9',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9225,c_9341])).

tff(c_9245,plain,(
    ! [B_859,A_860] : k3_xboole_0(B_859,A_860) = k3_xboole_0(A_860,B_859) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_9261,plain,(
    ! [A_860] : k3_xboole_0('#skF_9',A_860) = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_9245,c_9235])).

tff(c_9349,plain,(
    ! [A_865,B_866,C_867] :
      ( ~ r1_xboole_0(A_865,B_866)
      | ~ r2_hidden(C_867,k3_xboole_0(A_865,B_866)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_9352,plain,(
    ! [A_860,C_867] :
      ( ~ r1_xboole_0('#skF_9',A_860)
      | ~ r2_hidden(C_867,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9261,c_9349])).

tff(c_9363,plain,(
    ! [C_867] : ~ r2_hidden(C_867,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9345,c_9352])).

tff(c_10442,plain,(
    ! [A_976,C_977] :
      ( r2_hidden('#skF_5'(A_976,'#skF_9',C_977),C_977)
      | k2_zfmisc_1(A_976,'#skF_9') = C_977 ) ),
    inference(resolution,[status(thm)],[c_9816,c_9363])).

tff(c_10546,plain,(
    ! [A_976] : k2_zfmisc_1(A_976,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_10442,c_9363])).

tff(c_9212,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9210,c_7777])).

tff(c_10558,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10546,c_9212])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:19:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.21/2.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.21/2.28  
% 6.21/2.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.21/2.28  %$ r2_hidden > r1_xboole_0 > k5_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1
% 6.21/2.28  
% 6.21/2.28  %Foreground sorts:
% 6.21/2.28  
% 6.21/2.28  
% 6.21/2.28  %Background operators:
% 6.21/2.28  
% 6.21/2.28  
% 6.21/2.28  %Foreground operators:
% 6.21/2.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.21/2.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.21/2.28  tff('#skF_11', type, '#skF_11': $i).
% 6.21/2.28  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.21/2.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.21/2.28  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 6.21/2.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.21/2.28  tff('#skF_10', type, '#skF_10': $i).
% 6.21/2.28  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 6.21/2.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.21/2.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.21/2.28  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 6.21/2.28  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 6.21/2.28  tff('#skF_9', type, '#skF_9': $i).
% 6.21/2.28  tff('#skF_8', type, '#skF_8': $i).
% 6.21/2.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.21/2.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.21/2.28  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.21/2.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.21/2.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.21/2.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.21/2.28  
% 6.47/2.31  tff(f_59, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 6.47/2.31  tff(f_66, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.47/2.31  tff(f_47, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 6.47/2.31  tff(f_45, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 6.47/2.31  tff(f_43, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l97_xboole_1)).
% 6.47/2.31  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.47/2.31  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.47/2.31  tff(c_9816, plain, (![A_928, B_929, C_930]: (r2_hidden('#skF_4'(A_928, B_929, C_930), B_929) | r2_hidden('#skF_5'(A_928, B_929, C_930), C_930) | k2_zfmisc_1(A_928, B_929)=C_930)), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.47/2.31  tff(c_8690, plain, (![A_835, B_836, C_837]: (r2_hidden('#skF_4'(A_835, B_836, C_837), B_836) | r2_hidden('#skF_5'(A_835, B_836, C_837), C_837) | k2_zfmisc_1(A_835, B_836)=C_837)), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.47/2.31  tff(c_6926, plain, (![A_681, B_682, C_683]: (r2_hidden('#skF_4'(A_681, B_682, C_683), B_682) | r2_hidden('#skF_5'(A_681, B_682, C_683), C_683) | k2_zfmisc_1(A_681, B_682)=C_683)), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.47/2.31  tff(c_2467, plain, (![A_289, B_290, C_291]: (r2_hidden('#skF_4'(A_289, B_290, C_291), B_290) | r2_hidden('#skF_5'(A_289, B_290, C_291), C_291) | k2_zfmisc_1(A_289, B_290)=C_291)), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.47/2.31  tff(c_40, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.47/2.31  tff(c_66, plain, (k1_xboole_0!='#skF_11'), inference(splitLeft, [status(thm)], [c_40])).
% 6.47/2.31  tff(c_1430, plain, (![A_198, B_199, C_200]: (r2_hidden('#skF_4'(A_198, B_199, C_200), B_199) | r2_hidden('#skF_5'(A_198, B_199, C_200), C_200) | k2_zfmisc_1(A_198, B_199)=C_200)), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.47/2.31  tff(c_42, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0 | k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.47/2.31  tff(c_65, plain, (k1_xboole_0!='#skF_10'), inference(splitLeft, [status(thm)], [c_42])).
% 6.47/2.31  tff(c_651, plain, (![A_129, B_130, C_131]: (r2_hidden('#skF_4'(A_129, B_130, C_131), B_130) | r2_hidden('#skF_5'(A_129, B_130, C_131), C_131) | k2_zfmisc_1(A_129, B_130)=C_131)), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.47/2.31  tff(c_12, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.47/2.31  tff(c_10, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.47/2.31  tff(c_150, plain, (![A_51, B_52]: (r1_xboole_0(k3_xboole_0(A_51, B_52), k5_xboole_0(A_51, B_52)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.47/2.31  tff(c_162, plain, (![A_10]: (r1_xboole_0(k1_xboole_0, k5_xboole_0(A_10, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_150])).
% 6.47/2.31  tff(c_166, plain, (![A_10]: (r1_xboole_0(k1_xboole_0, A_10))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_162])).
% 6.47/2.31  tff(c_67, plain, (![B_48, A_49]: (k3_xboole_0(B_48, A_49)=k3_xboole_0(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.47/2.31  tff(c_83, plain, (![A_49]: (k3_xboole_0(k1_xboole_0, A_49)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_67, c_10])).
% 6.47/2.31  tff(c_199, plain, (![A_56, B_57, C_58]: (~r1_xboole_0(A_56, B_57) | ~r2_hidden(C_58, k3_xboole_0(A_56, B_57)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.47/2.31  tff(c_202, plain, (![A_49, C_58]: (~r1_xboole_0(k1_xboole_0, A_49) | ~r2_hidden(C_58, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_83, c_199])).
% 6.47/2.31  tff(c_213, plain, (![C_58]: (~r2_hidden(C_58, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_166, c_202])).
% 6.47/2.31  tff(c_48, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k2_zfmisc_1('#skF_10', '#skF_11')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.47/2.31  tff(c_169, plain, (k2_zfmisc_1('#skF_10', '#skF_11')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_48])).
% 6.47/2.31  tff(c_272, plain, (![E_68, F_69, A_70, B_71]: (r2_hidden(k4_tarski(E_68, F_69), k2_zfmisc_1(A_70, B_71)) | ~r2_hidden(F_69, B_71) | ~r2_hidden(E_68, A_70))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.47/2.31  tff(c_275, plain, (![E_68, F_69]: (r2_hidden(k4_tarski(E_68, F_69), k1_xboole_0) | ~r2_hidden(F_69, '#skF_11') | ~r2_hidden(E_68, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_169, c_272])).
% 6.47/2.31  tff(c_276, plain, (![F_69, E_68]: (~r2_hidden(F_69, '#skF_11') | ~r2_hidden(E_68, '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_213, c_275])).
% 6.47/2.31  tff(c_277, plain, (![E_68]: (~r2_hidden(E_68, '#skF_10'))), inference(splitLeft, [status(thm)], [c_276])).
% 6.47/2.31  tff(c_916, plain, (![A_144, C_145]: (r2_hidden('#skF_5'(A_144, '#skF_10', C_145), C_145) | k2_zfmisc_1(A_144, '#skF_10')=C_145)), inference(resolution, [status(thm)], [c_651, c_277])).
% 6.47/2.31  tff(c_1023, plain, (![A_144]: (k2_zfmisc_1(A_144, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_916, c_277])).
% 6.47/2.31  tff(c_1025, plain, (![A_144]: (k2_zfmisc_1(A_144, '#skF_10')=k1_xboole_0)), inference(resolution, [status(thm)], [c_916, c_213])).
% 6.47/2.31  tff(c_1091, plain, (k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1023, c_1025])).
% 6.47/2.31  tff(c_1092, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_1091])).
% 6.47/2.31  tff(c_1093, plain, (![F_69]: (~r2_hidden(F_69, '#skF_11'))), inference(splitRight, [status(thm)], [c_276])).
% 6.47/2.31  tff(c_1687, plain, (![A_213, C_214]: (r2_hidden('#skF_5'(A_213, '#skF_11', C_214), C_214) | k2_zfmisc_1(A_213, '#skF_11')=C_214)), inference(resolution, [status(thm)], [c_1430, c_1093])).
% 6.47/2.31  tff(c_1789, plain, (![A_213]: (k2_zfmisc_1(A_213, '#skF_11')='#skF_11')), inference(resolution, [status(thm)], [c_1687, c_1093])).
% 6.47/2.31  tff(c_1801, plain, (k1_xboole_0='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_1789, c_169])).
% 6.47/2.31  tff(c_1803, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_1801])).
% 6.47/2.31  tff(c_1804, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_48])).
% 6.47/2.31  tff(c_1807, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_1804])).
% 6.47/2.31  tff(c_1808, plain, (![A_10]: (r1_xboole_0('#skF_9', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_1807, c_166])).
% 6.47/2.31  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.47/2.31  tff(c_1831, plain, (![A_217]: (k3_xboole_0(A_217, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1807, c_1807, c_10])).
% 6.47/2.31  tff(c_1852, plain, (![B_2]: (k3_xboole_0('#skF_9', B_2)='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_2, c_1831])).
% 6.47/2.31  tff(c_1898, plain, (![A_219, B_220, C_221]: (~r1_xboole_0(A_219, B_220) | ~r2_hidden(C_221, k3_xboole_0(A_219, B_220)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.47/2.31  tff(c_1901, plain, (![B_2, C_221]: (~r1_xboole_0('#skF_9', B_2) | ~r2_hidden(C_221, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1852, c_1898])).
% 6.47/2.31  tff(c_1912, plain, (![C_221]: (~r2_hidden(C_221, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_1808, c_1901])).
% 6.47/2.31  tff(c_3551, plain, (![A_362, C_363]: (r2_hidden('#skF_5'(A_362, '#skF_9', C_363), C_363) | k2_zfmisc_1(A_362, '#skF_9')=C_363)), inference(resolution, [status(thm)], [c_2467, c_1912])).
% 6.47/2.31  tff(c_3600, plain, (![A_362]: (k2_zfmisc_1(A_362, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_3551, c_1912])).
% 6.47/2.31  tff(c_46, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0 | k2_zfmisc_1('#skF_10', '#skF_11')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.47/2.31  tff(c_1856, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_9' | k2_zfmisc_1('#skF_10', '#skF_11')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1807, c_1807, c_46])).
% 6.47/2.31  tff(c_1857, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_9'), inference(splitLeft, [status(thm)], [c_1856])).
% 6.47/2.31  tff(c_3612, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3600, c_1857])).
% 6.47/2.31  tff(c_3613, plain, (k2_zfmisc_1('#skF_10', '#skF_11')='#skF_9'), inference(splitRight, [status(thm)], [c_1856])).
% 6.47/2.31  tff(c_1805, plain, (k2_zfmisc_1('#skF_10', '#skF_11')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 6.47/2.31  tff(c_3624, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3613, c_1807, c_1805])).
% 6.47/2.31  tff(c_3625, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_1804])).
% 6.47/2.31  tff(c_4936, plain, (k2_zfmisc_1('#skF_10', '#skF_11')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_3625, c_1805])).
% 6.47/2.31  tff(c_4138, plain, (![A_423, B_424, C_425]: (r2_hidden('#skF_3'(A_423, B_424, C_425), A_423) | r2_hidden('#skF_5'(A_423, B_424, C_425), C_425) | k2_zfmisc_1(A_423, B_424)=C_425)), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.47/2.31  tff(c_3627, plain, (![A_10]: (r1_xboole_0('#skF_8', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_3625, c_166])).
% 6.47/2.31  tff(c_3628, plain, (![A_49]: (k3_xboole_0('#skF_8', A_49)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3625, c_3625, c_83])).
% 6.47/2.31  tff(c_3718, plain, (![A_368, B_369, C_370]: (~r1_xboole_0(A_368, B_369) | ~r2_hidden(C_370, k3_xboole_0(A_368, B_369)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.47/2.31  tff(c_3721, plain, (![A_49, C_370]: (~r1_xboole_0('#skF_8', A_49) | ~r2_hidden(C_370, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_3628, c_3718])).
% 6.47/2.31  tff(c_3732, plain, (![C_370]: (~r2_hidden(C_370, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_3627, c_3721])).
% 6.47/2.31  tff(c_4817, plain, (![A_484, B_485]: (r2_hidden('#skF_3'(A_484, B_485, '#skF_8'), A_484) | k2_zfmisc_1(A_484, B_485)='#skF_8')), inference(resolution, [status(thm)], [c_4138, c_3732])).
% 6.47/2.31  tff(c_4921, plain, (![B_485]: (k2_zfmisc_1('#skF_8', B_485)='#skF_8')), inference(resolution, [status(thm)], [c_4817, c_3732])).
% 6.47/2.31  tff(c_3638, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_8' | k2_zfmisc_1('#skF_10', '#skF_11')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_3625, c_3625, c_46])).
% 6.47/2.31  tff(c_3639, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_8'), inference(splitLeft, [status(thm)], [c_3638])).
% 6.47/2.31  tff(c_4932, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4921, c_3639])).
% 6.47/2.31  tff(c_4933, plain, (k2_zfmisc_1('#skF_10', '#skF_11')='#skF_8'), inference(splitRight, [status(thm)], [c_3638])).
% 6.47/2.31  tff(c_4953, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4936, c_4933])).
% 6.47/2.31  tff(c_4955, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_40])).
% 6.47/2.31  tff(c_4954, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_40])).
% 6.47/2.31  tff(c_4965, plain, ('#skF_11'='#skF_8' | '#skF_11'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_4955, c_4955, c_4954])).
% 6.47/2.31  tff(c_4966, plain, ('#skF_11'='#skF_9'), inference(splitLeft, [status(thm)], [c_4965])).
% 6.47/2.31  tff(c_4958, plain, (![A_11]: (k5_xboole_0(A_11, '#skF_11')=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_4955, c_12])).
% 6.47/2.31  tff(c_4978, plain, (![A_11]: (k5_xboole_0(A_11, '#skF_9')=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_4966, c_4958])).
% 6.47/2.31  tff(c_4957, plain, (![A_10]: (k3_xboole_0(A_10, '#skF_11')='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_4955, c_4955, c_10])).
% 6.47/2.31  tff(c_4988, plain, (![A_10]: (k3_xboole_0(A_10, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_4966, c_4966, c_4957])).
% 6.47/2.31  tff(c_5080, plain, (![A_493, B_494]: (r1_xboole_0(k3_xboole_0(A_493, B_494), k5_xboole_0(A_493, B_494)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.47/2.31  tff(c_5092, plain, (![A_10]: (r1_xboole_0('#skF_9', k5_xboole_0(A_10, '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_4988, c_5080])).
% 6.47/2.31  tff(c_5096, plain, (![A_10]: (r1_xboole_0('#skF_9', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_4978, c_5092])).
% 6.47/2.31  tff(c_5831, plain, (![A_584, B_585, C_586]: (r2_hidden('#skF_4'(A_584, B_585, C_586), B_585) | r2_hidden('#skF_5'(A_584, B_585, C_586), C_586) | k2_zfmisc_1(A_584, B_585)=C_586)), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.47/2.31  tff(c_5098, plain, (![A_495, B_496, C_497]: (~r1_xboole_0(A_495, B_496) | ~r2_hidden(C_497, k3_xboole_0(A_495, B_496)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.47/2.31  tff(c_5110, plain, (![A_10, C_497]: (~r1_xboole_0(A_10, '#skF_9') | ~r2_hidden(C_497, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_4988, c_5098])).
% 6.47/2.31  tff(c_5115, plain, (![C_497]: (~r2_hidden(C_497, '#skF_9'))), inference(splitLeft, [status(thm)], [c_5110])).
% 6.47/2.31  tff(c_6195, plain, (![A_607, C_608]: (r2_hidden('#skF_5'(A_607, '#skF_9', C_608), C_608) | k2_zfmisc_1(A_607, '#skF_9')=C_608)), inference(resolution, [status(thm)], [c_5831, c_5115])).
% 6.47/2.31  tff(c_6299, plain, (![A_607]: (k2_zfmisc_1(A_607, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_6195, c_5115])).
% 6.47/2.31  tff(c_38, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0 | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.47/2.31  tff(c_4964, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_4955, c_4955, c_38])).
% 6.47/2.31  tff(c_4968, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_4966, c_4964])).
% 6.47/2.31  tff(c_6311, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6299, c_4968])).
% 6.47/2.31  tff(c_6313, plain, (![A_609]: (~r1_xboole_0(A_609, '#skF_9'))), inference(splitRight, [status(thm)], [c_5110])).
% 6.47/2.31  tff(c_6318, plain, $false, inference(resolution, [status(thm)], [c_5096, c_6313])).
% 6.47/2.31  tff(c_6319, plain, ('#skF_11'='#skF_8'), inference(splitRight, [status(thm)], [c_4965])).
% 6.47/2.31  tff(c_6334, plain, (![A_11]: (k5_xboole_0(A_11, '#skF_8')=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_6319, c_4958])).
% 6.47/2.31  tff(c_6344, plain, (![A_10]: (k3_xboole_0(A_10, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_6319, c_6319, c_4957])).
% 6.47/2.31  tff(c_6437, plain, (![A_615, B_616]: (r1_xboole_0(k3_xboole_0(A_615, B_616), k5_xboole_0(A_615, B_616)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.47/2.31  tff(c_6449, plain, (![A_10]: (r1_xboole_0('#skF_8', k5_xboole_0(A_10, '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_6344, c_6437])).
% 6.47/2.31  tff(c_6453, plain, (![A_10]: (r1_xboole_0('#skF_8', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_6334, c_6449])).
% 6.47/2.31  tff(c_6352, plain, (![B_612, A_613]: (k3_xboole_0(B_612, A_613)=k3_xboole_0(A_613, B_612))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.47/2.31  tff(c_6368, plain, (![A_613]: (k3_xboole_0('#skF_8', A_613)='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_6352, c_6344])).
% 6.47/2.31  tff(c_6456, plain, (![A_618, B_619, C_620]: (~r1_xboole_0(A_618, B_619) | ~r2_hidden(C_620, k3_xboole_0(A_618, B_619)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.47/2.31  tff(c_6459, plain, (![A_613, C_620]: (~r1_xboole_0('#skF_8', A_613) | ~r2_hidden(C_620, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_6368, c_6456])).
% 6.47/2.31  tff(c_6470, plain, (![C_620]: (~r2_hidden(C_620, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_6453, c_6459])).
% 6.47/2.31  tff(c_7561, plain, (![A_727, C_728]: (r2_hidden('#skF_5'(A_727, '#skF_8', C_728), C_728) | k2_zfmisc_1(A_727, '#skF_8')=C_728)), inference(resolution, [status(thm)], [c_6926, c_6470])).
% 6.47/2.31  tff(c_7665, plain, (![A_727]: (k2_zfmisc_1(A_727, '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_7561, c_6470])).
% 6.47/2.31  tff(c_6644, plain, (![A_648, B_649, D_650]: (r2_hidden('#skF_6'(A_648, B_649, k2_zfmisc_1(A_648, B_649), D_650), A_648) | ~r2_hidden(D_650, k2_zfmisc_1(A_648, B_649)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.47/2.31  tff(c_6668, plain, (![D_650, B_649]: (~r2_hidden(D_650, k2_zfmisc_1('#skF_8', B_649)))), inference(resolution, [status(thm)], [c_6644, c_6470])).
% 6.47/2.31  tff(c_7661, plain, (![A_727, B_649]: (k2_zfmisc_1(A_727, '#skF_8')=k2_zfmisc_1('#skF_8', B_649))), inference(resolution, [status(thm)], [c_7561, c_6668])).
% 6.47/2.31  tff(c_7754, plain, (![B_649]: (k2_zfmisc_1('#skF_8', B_649)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_7665, c_7661])).
% 6.47/2.31  tff(c_6323, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_6319, c_4964])).
% 6.47/2.31  tff(c_7768, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7754, c_6323])).
% 6.47/2.31  tff(c_7770, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_42])).
% 6.47/2.31  tff(c_44, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.47/2.31  tff(c_7779, plain, ('#skF_10'='#skF_9' | '#skF_10'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_7770, c_7770, c_7770, c_44])).
% 6.47/2.31  tff(c_7780, plain, ('#skF_10'='#skF_8'), inference(splitLeft, [status(thm)], [c_7779])).
% 6.47/2.31  tff(c_7772, plain, (![A_11]: (k5_xboole_0(A_11, '#skF_10')=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_7770, c_12])).
% 6.47/2.31  tff(c_7791, plain, (![A_11]: (k5_xboole_0(A_11, '#skF_8')=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_7780, c_7772])).
% 6.47/2.31  tff(c_7771, plain, (![A_10]: (k3_xboole_0(A_10, '#skF_10')='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_7770, c_7770, c_10])).
% 6.47/2.31  tff(c_7801, plain, (![A_10]: (k3_xboole_0(A_10, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_7780, c_7780, c_7771])).
% 6.47/2.31  tff(c_7894, plain, (![A_740, B_741]: (r1_xboole_0(k3_xboole_0(A_740, B_741), k5_xboole_0(A_740, B_741)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.47/2.31  tff(c_7906, plain, (![A_10]: (r1_xboole_0('#skF_8', k5_xboole_0(A_10, '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_7801, c_7894])).
% 6.47/2.31  tff(c_7910, plain, (![A_10]: (r1_xboole_0('#skF_8', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_7791, c_7906])).
% 6.47/2.31  tff(c_7810, plain, (![B_737, A_738]: (k3_xboole_0(B_737, A_738)=k3_xboole_0(A_738, B_737))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.47/2.31  tff(c_7826, plain, (![A_738]: (k3_xboole_0('#skF_8', A_738)='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_7810, c_7801])).
% 6.47/2.31  tff(c_7914, plain, (![A_743, B_744, C_745]: (~r1_xboole_0(A_743, B_744) | ~r2_hidden(C_745, k3_xboole_0(A_743, B_744)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.47/2.31  tff(c_7917, plain, (![A_738, C_745]: (~r1_xboole_0('#skF_8', A_738) | ~r2_hidden(C_745, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_7826, c_7914])).
% 6.47/2.31  tff(c_7928, plain, (![C_745]: (~r2_hidden(C_745, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_7910, c_7917])).
% 6.47/2.31  tff(c_9004, plain, (![A_849, C_850]: (r2_hidden('#skF_5'(A_849, '#skF_8', C_850), C_850) | k2_zfmisc_1(A_849, '#skF_8')=C_850)), inference(resolution, [status(thm)], [c_8690, c_7928])).
% 6.47/2.31  tff(c_9108, plain, (![A_849]: (k2_zfmisc_1(A_849, '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_9004, c_7928])).
% 6.47/2.31  tff(c_8135, plain, (![A_779, B_780, D_781]: (r2_hidden('#skF_6'(A_779, B_780, k2_zfmisc_1(A_779, B_780), D_781), A_779) | ~r2_hidden(D_781, k2_zfmisc_1(A_779, B_780)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.47/2.31  tff(c_8164, plain, (![D_781, B_780]: (~r2_hidden(D_781, k2_zfmisc_1('#skF_8', B_780)))), inference(resolution, [status(thm)], [c_8135, c_7928])).
% 6.47/2.31  tff(c_9103, plain, (![A_849, B_780]: (k2_zfmisc_1(A_849, '#skF_8')=k2_zfmisc_1('#skF_8', B_780))), inference(resolution, [status(thm)], [c_9004, c_8164])).
% 6.47/2.31  tff(c_9195, plain, (![B_780]: (k2_zfmisc_1('#skF_8', B_780)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_9108, c_9103])).
% 6.47/2.31  tff(c_7769, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 6.47/2.31  tff(c_7777, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_7770, c_7769])).
% 6.47/2.31  tff(c_7781, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_7780, c_7777])).
% 6.47/2.31  tff(c_9209, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9195, c_7781])).
% 6.47/2.31  tff(c_9210, plain, ('#skF_10'='#skF_9'), inference(splitRight, [status(thm)], [c_7779])).
% 6.47/2.31  tff(c_9225, plain, (![A_11]: (k5_xboole_0(A_11, '#skF_9')=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_9210, c_7772])).
% 6.47/2.31  tff(c_9235, plain, (![A_10]: (k3_xboole_0(A_10, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_9210, c_9210, c_7771])).
% 6.47/2.31  tff(c_9329, plain, (![A_862, B_863]: (r1_xboole_0(k3_xboole_0(A_862, B_863), k5_xboole_0(A_862, B_863)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.47/2.31  tff(c_9341, plain, (![A_10]: (r1_xboole_0('#skF_9', k5_xboole_0(A_10, '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_9235, c_9329])).
% 6.47/2.31  tff(c_9345, plain, (![A_10]: (r1_xboole_0('#skF_9', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_9225, c_9341])).
% 6.47/2.31  tff(c_9245, plain, (![B_859, A_860]: (k3_xboole_0(B_859, A_860)=k3_xboole_0(A_860, B_859))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.47/2.31  tff(c_9261, plain, (![A_860]: (k3_xboole_0('#skF_9', A_860)='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_9245, c_9235])).
% 6.47/2.31  tff(c_9349, plain, (![A_865, B_866, C_867]: (~r1_xboole_0(A_865, B_866) | ~r2_hidden(C_867, k3_xboole_0(A_865, B_866)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.47/2.31  tff(c_9352, plain, (![A_860, C_867]: (~r1_xboole_0('#skF_9', A_860) | ~r2_hidden(C_867, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_9261, c_9349])).
% 6.47/2.31  tff(c_9363, plain, (![C_867]: (~r2_hidden(C_867, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_9345, c_9352])).
% 6.47/2.31  tff(c_10442, plain, (![A_976, C_977]: (r2_hidden('#skF_5'(A_976, '#skF_9', C_977), C_977) | k2_zfmisc_1(A_976, '#skF_9')=C_977)), inference(resolution, [status(thm)], [c_9816, c_9363])).
% 6.47/2.31  tff(c_10546, plain, (![A_976]: (k2_zfmisc_1(A_976, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_10442, c_9363])).
% 6.47/2.31  tff(c_9212, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_9210, c_7777])).
% 6.47/2.31  tff(c_10558, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10546, c_9212])).
% 6.47/2.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.47/2.31  
% 6.47/2.31  Inference rules
% 6.47/2.31  ----------------------
% 6.47/2.31  #Ref     : 0
% 6.47/2.31  #Sup     : 2199
% 6.47/2.31  #Fact    : 0
% 6.47/2.31  #Define  : 0
% 6.47/2.31  #Split   : 11
% 6.47/2.31  #Chain   : 0
% 6.47/2.31  #Close   : 0
% 6.47/2.31  
% 6.47/2.31  Ordering : KBO
% 6.47/2.31  
% 6.47/2.31  Simplification rules
% 6.47/2.31  ----------------------
% 6.47/2.31  #Subsume      : 668
% 6.47/2.31  #Demod        : 719
% 6.47/2.31  #Tautology    : 455
% 6.47/2.31  #SimpNegUnit  : 51
% 6.47/2.31  #BackRed      : 120
% 6.47/2.31  
% 6.47/2.31  #Partial instantiations: 0
% 6.47/2.31  #Strategies tried      : 1
% 6.47/2.31  
% 6.47/2.31  Timing (in seconds)
% 6.47/2.31  ----------------------
% 6.47/2.31  Preprocessing        : 0.30
% 6.47/2.31  Parsing              : 0.15
% 6.47/2.31  CNF conversion       : 0.02
% 6.47/2.31  Main loop            : 1.18
% 6.47/2.31  Inferencing          : 0.46
% 6.47/2.31  Reduction            : 0.35
% 6.47/2.31  Demodulation         : 0.23
% 6.47/2.31  BG Simplification    : 0.05
% 6.47/2.31  Subsumption          : 0.20
% 6.47/2.31  Abstraction          : 0.08
% 6.47/2.31  MUC search           : 0.00
% 6.47/2.31  Cooper               : 0.00
% 6.47/2.31  Total                : 1.55
% 6.47/2.31  Index Insertion      : 0.00
% 6.47/2.31  Index Deletion       : 0.00
% 6.47/2.31  Index Matching       : 0.00
% 6.47/2.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
