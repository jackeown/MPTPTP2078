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
% DateTime   : Thu Dec  3 09:53:43 EST 2020

% Result     : Theorem 6.43s
% Output     : CNFRefutation 6.89s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 551 expanded)
%              Number of leaves         :   29 ( 177 expanded)
%              Depth                    :   11
%              Number of atoms          :  187 (1036 expanded)
%              Number of equality atoms :  100 ( 698 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_11611,plain,(
    ! [A_1223,B_1224,C_1225] :
      ( r2_hidden('#skF_3'(A_1223,B_1224,C_1225),B_1224)
      | r2_hidden('#skF_4'(A_1223,B_1224,C_1225),C_1225)
      | k2_zfmisc_1(A_1223,B_1224) = C_1225 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10585,plain,(
    ! [A_1132,B_1133,C_1134] :
      ( r2_hidden('#skF_2'(A_1132,B_1133,C_1134),A_1132)
      | r2_hidden('#skF_4'(A_1132,B_1133,C_1134),C_1134)
      | k2_zfmisc_1(A_1132,B_1133) = C_1134 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_9617,plain,(
    ! [A_1010,B_1011,C_1012] :
      ( r2_hidden('#skF_2'(A_1010,B_1011,C_1012),A_1010)
      | r2_hidden('#skF_4'(A_1010,B_1011,C_1012),C_1012)
      | k2_zfmisc_1(A_1010,B_1011) = C_1012 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_52,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_7347,plain,(
    ! [A_774,B_775,C_776] :
      ( r2_hidden('#skF_3'(A_774,B_775,C_776),B_775)
      | r2_hidden('#skF_4'(A_774,B_775,C_776),C_776)
      | k2_zfmisc_1(A_774,B_775) = C_776 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_54,plain,
    ( k2_zfmisc_1('#skF_7','#skF_8') != k1_xboole_0
    | k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_71,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_6488,plain,(
    ! [A_695,B_696,C_697] :
      ( r2_hidden('#skF_2'(A_695,B_696,C_697),A_695)
      | r2_hidden('#skF_4'(A_695,B_696,C_697),C_697)
      | k2_zfmisc_1(A_695,B_696) = C_697 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4012,plain,(
    ! [A_439,B_440] :
      ( k4_xboole_0(A_439,B_440) = k1_xboole_0
      | ~ r1_tarski(A_439,B_440) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4022,plain,(
    ! [A_443,B_444] : k4_xboole_0(k4_xboole_0(A_443,B_444),A_443) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_4012])).

tff(c_46,plain,(
    ! [C_51,B_50] : ~ r2_hidden(C_51,k4_xboole_0(B_50,k1_tarski(C_51))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4030,plain,(
    ! [C_51] : ~ r2_hidden(C_51,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4022,c_46])).

tff(c_3417,plain,(
    ! [A_418,B_419,C_420] :
      ( r2_hidden('#skF_2'(A_418,B_419,C_420),A_418)
      | r2_hidden('#skF_4'(A_418,B_419,C_420),C_420)
      | k2_zfmisc_1(A_418,B_419) = C_420 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2288,plain,(
    ! [A_300,B_301,C_302] :
      ( r2_hidden('#skF_3'(A_300,B_301,C_302),B_301)
      | r2_hidden('#skF_4'(A_300,B_301,C_302),C_302)
      | k2_zfmisc_1(A_300,B_301) = C_302 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1590,plain,(
    ! [A_197,B_198,C_199] :
      ( r2_hidden('#skF_3'(A_197,B_198,C_199),B_198)
      | r2_hidden('#skF_4'(A_197,B_198,C_199),C_199)
      | k2_zfmisc_1(A_197,B_198) = C_199 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1232,plain,(
    ! [A_156,B_157,C_158] :
      ( r2_hidden('#skF_2'(A_156,B_157,C_158),A_156)
      | r2_hidden('#skF_4'(A_156,B_157,C_158),C_158)
      | k2_zfmisc_1(A_156,B_157) = C_158 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_85,plain,(
    ! [A_61,B_62] :
      ( k4_xboole_0(A_61,B_62) = k1_xboole_0
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_94,plain,(
    ! [A_63,B_64] : k4_xboole_0(k4_xboole_0(A_63,B_64),A_63) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_85])).

tff(c_102,plain,(
    ! [C_51] : ~ r2_hidden(C_51,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_46])).

tff(c_60,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_9','#skF_10') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_113,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_215,plain,(
    ! [A_87,B_88,C_89,D_90] :
      ( r2_hidden(k4_tarski(A_87,B_88),k2_zfmisc_1(C_89,D_90))
      | ~ r2_hidden(B_88,D_90)
      | ~ r2_hidden(A_87,C_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_224,plain,(
    ! [A_87,B_88] :
      ( r2_hidden(k4_tarski(A_87,B_88),k1_xboole_0)
      | ~ r2_hidden(B_88,'#skF_10')
      | ~ r2_hidden(A_87,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_215])).

tff(c_227,plain,(
    ! [B_88,A_87] :
      ( ~ r2_hidden(B_88,'#skF_10')
      | ~ r2_hidden(A_87,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_224])).

tff(c_228,plain,(
    ! [A_87] : ~ r2_hidden(A_87,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_227])).

tff(c_1318,plain,(
    ! [A_159,B_160] :
      ( r2_hidden('#skF_2'(A_159,B_160,'#skF_9'),A_159)
      | k2_zfmisc_1(A_159,B_160) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_1232,c_228])).

tff(c_1360,plain,(
    ! [B_160] : k2_zfmisc_1('#skF_9',B_160) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1318,c_228])).

tff(c_1367,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1360,c_113])).

tff(c_1371,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_1367])).

tff(c_1372,plain,(
    ! [B_88] : ~ r2_hidden(B_88,'#skF_10') ),
    inference(splitRight,[status(thm)],[c_227])).

tff(c_1801,plain,(
    ! [A_209,B_210] :
      ( r2_hidden('#skF_3'(A_209,B_210,'#skF_10'),B_210)
      | k2_zfmisc_1(A_209,B_210) = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_1590,c_1372])).

tff(c_1883,plain,(
    ! [A_209] : k2_zfmisc_1(A_209,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_1801,c_1372])).

tff(c_1889,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1883,c_113])).

tff(c_1891,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1889])).

tff(c_1892,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1895,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1892])).

tff(c_1896,plain,(
    ! [C_51] : ~ r2_hidden(C_51,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1895,c_102])).

tff(c_2708,plain,(
    ! [A_318,B_319] :
      ( r2_hidden('#skF_3'(A_318,B_319,'#skF_8'),B_319)
      | k2_zfmisc_1(A_318,B_319) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_2288,c_1896])).

tff(c_2802,plain,(
    ! [A_318] : k2_zfmisc_1(A_318,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_2708,c_1896])).

tff(c_58,plain,
    ( k2_zfmisc_1('#skF_7','#skF_8') != k1_xboole_0
    | k2_zfmisc_1('#skF_9','#skF_10') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_74,plain,(
    k2_zfmisc_1('#skF_7','#skF_8') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_1900,plain,(
    k2_zfmisc_1('#skF_7','#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1895,c_74])).

tff(c_2813,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2802,c_1900])).

tff(c_2814,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1892])).

tff(c_2817,plain,(
    ! [C_51] : ~ r2_hidden(C_51,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2814,c_102])).

tff(c_3957,plain,(
    ! [A_437,B_438] :
      ( r2_hidden('#skF_2'(A_437,B_438,'#skF_7'),A_437)
      | k2_zfmisc_1(A_437,B_438) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_3417,c_2817])).

tff(c_3991,plain,(
    ! [B_438] : k2_zfmisc_1('#skF_7',B_438) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_3957,c_2817])).

tff(c_2821,plain,(
    k2_zfmisc_1('#skF_7','#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2814,c_74])).

tff(c_4001,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3991,c_2821])).

tff(c_4002,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_4161,plain,(
    ! [A_475,B_476,C_477,D_478] :
      ( r2_hidden(k4_tarski(A_475,B_476),k2_zfmisc_1(C_477,D_478))
      | ~ r2_hidden(B_476,D_478)
      | ~ r2_hidden(A_475,C_477) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4173,plain,(
    ! [A_475,B_476] :
      ( r2_hidden(k4_tarski(A_475,B_476),k1_xboole_0)
      | ~ r2_hidden(B_476,'#skF_10')
      | ~ r2_hidden(A_475,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4002,c_4161])).

tff(c_4177,plain,(
    ! [B_476,A_475] :
      ( ~ r2_hidden(B_476,'#skF_10')
      | ~ r2_hidden(A_475,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_4030,c_4173])).

tff(c_6102,plain,(
    ! [A_475] : ~ r2_hidden(A_475,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_4177])).

tff(c_6800,plain,(
    ! [A_710,B_711] :
      ( r2_hidden('#skF_2'(A_710,B_711,'#skF_9'),A_710)
      | k2_zfmisc_1(A_710,B_711) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_6488,c_6102])).

tff(c_6929,plain,(
    ! [B_711] : k2_zfmisc_1('#skF_9',B_711) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_6800,c_6102])).

tff(c_6940,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6929,c_4002])).

tff(c_6942,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_6940])).

tff(c_6943,plain,(
    ! [B_476] : ~ r2_hidden(B_476,'#skF_10') ),
    inference(splitRight,[status(thm)],[c_4177])).

tff(c_7669,plain,(
    ! [A_789,B_790] :
      ( r2_hidden('#skF_3'(A_789,B_790,'#skF_10'),B_790)
      | k2_zfmisc_1(A_789,B_790) = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_7347,c_6943])).

tff(c_7803,plain,(
    ! [A_789] : k2_zfmisc_1(A_789,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_7669,c_6943])).

tff(c_7815,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7803,c_4002])).

tff(c_7817,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_7815])).

tff(c_7819,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_9050,plain,(
    ! [A_916,B_917] :
      ( k4_xboole_0(A_916,B_917) = '#skF_10'
      | ~ r1_tarski(A_916,B_917) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7819,c_4])).

tff(c_9060,plain,(
    ! [A_918,B_919] : k4_xboole_0(k4_xboole_0(A_918,B_919),A_918) = '#skF_10' ),
    inference(resolution,[status(thm)],[c_6,c_9050])).

tff(c_9068,plain,(
    ! [C_51] : ~ r2_hidden(C_51,'#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_9060,c_46])).

tff(c_9819,plain,(
    ! [A_1017,B_1018] :
      ( r2_hidden('#skF_2'(A_1017,B_1018,'#skF_10'),A_1017)
      | k2_zfmisc_1(A_1017,B_1018) = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_9617,c_9068])).

tff(c_9908,plain,(
    ! [B_1018] : k2_zfmisc_1('#skF_10',B_1018) = '#skF_10' ),
    inference(resolution,[status(thm)],[c_9819,c_9068])).

tff(c_8436,plain,(
    ! [A_893,B_894,C_895] :
      ( r2_hidden('#skF_3'(A_893,B_894,C_895),B_894)
      | r2_hidden('#skF_4'(A_893,B_894,C_895),C_895)
      | k2_zfmisc_1(A_893,B_894) = C_895 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_7818,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_7825,plain,
    ( '#skF_7' = '#skF_10'
    | '#skF_10' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7819,c_7819,c_7818])).

tff(c_7826,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_7825])).

tff(c_7828,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7826,c_7819])).

tff(c_7852,plain,(
    ! [A_795,B_796] :
      ( k4_xboole_0(A_795,B_796) = '#skF_8'
      | ~ r1_tarski(A_795,B_796) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7828,c_4])).

tff(c_7857,plain,(
    ! [A_797,B_798] : k4_xboole_0(k4_xboole_0(A_797,B_798),A_797) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_6,c_7852])).

tff(c_7865,plain,(
    ! [C_51] : ~ r2_hidden(C_51,'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_7857,c_46])).

tff(c_8991,plain,(
    ! [A_910,B_911] :
      ( r2_hidden('#skF_3'(A_910,B_911,'#skF_8'),B_911)
      | k2_zfmisc_1(A_910,B_911) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_8436,c_7865])).

tff(c_9025,plain,(
    ! [A_910] : k2_zfmisc_1(A_910,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_8991,c_7865])).

tff(c_50,plain,
    ( k2_zfmisc_1('#skF_7','#skF_8') != k1_xboole_0
    | k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_7838,plain,(
    k2_zfmisc_1('#skF_7','#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7828,c_7826,c_7828,c_50])).

tff(c_9035,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9025,c_7838])).

tff(c_9036,plain,(
    '#skF_7' = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_7825])).

tff(c_9046,plain,(
    k2_zfmisc_1('#skF_10','#skF_8') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7819,c_9036,c_7819,c_50])).

tff(c_9918,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9908,c_9046])).

tff(c_9920,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_9951,plain,(
    ! [A_1025,B_1026] :
      ( k4_xboole_0(A_1025,B_1026) = '#skF_9'
      | ~ r1_tarski(A_1025,B_1026) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9920,c_4])).

tff(c_9960,plain,(
    ! [A_1027,B_1028] : k4_xboole_0(k4_xboole_0(A_1027,B_1028),A_1027) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_6,c_9951])).

tff(c_9968,plain,(
    ! [C_51] : ~ r2_hidden(C_51,'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_9960,c_46])).

tff(c_11236,plain,(
    ! [A_1151,B_1152] :
      ( r2_hidden('#skF_2'(A_1151,B_1152,'#skF_9'),A_1151)
      | k2_zfmisc_1(A_1151,B_1152) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_10585,c_9968])).

tff(c_11280,plain,(
    ! [B_1152] : k2_zfmisc_1('#skF_9',B_1152) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_11236,c_9968])).

tff(c_56,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_9929,plain,
    ( '#skF_9' = '#skF_8'
    | '#skF_7' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9920,c_9920,c_9920,c_56])).

tff(c_9930,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_9929])).

tff(c_9919,plain,(
    k2_zfmisc_1('#skF_7','#skF_8') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_9927,plain,(
    k2_zfmisc_1('#skF_7','#skF_8') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9920,c_9919])).

tff(c_9931,plain,(
    k2_zfmisc_1('#skF_9','#skF_8') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9930,c_9927])).

tff(c_11292,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11280,c_9931])).

tff(c_11293,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_9929])).

tff(c_11297,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11293,c_9920])).

tff(c_11320,plain,(
    ! [A_1157,B_1158] :
      ( k4_xboole_0(A_1157,B_1158) = '#skF_8'
      | ~ r1_tarski(A_1157,B_1158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11297,c_4])).

tff(c_11325,plain,(
    ! [A_1159,B_1160] : k4_xboole_0(k4_xboole_0(A_1159,B_1160),A_1159) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_6,c_11320])).

tff(c_11333,plain,(
    ! [C_51] : ~ r2_hidden(C_51,'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_11325,c_46])).

tff(c_12522,plain,(
    ! [A_1279,B_1280] :
      ( r2_hidden('#skF_3'(A_1279,B_1280,'#skF_8'),B_1280)
      | k2_zfmisc_1(A_1279,B_1280) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_11611,c_11333])).

tff(c_12561,plain,(
    ! [A_1279] : k2_zfmisc_1(A_1279,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_12522,c_11333])).

tff(c_11295,plain,(
    k2_zfmisc_1('#skF_7','#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11293,c_9927])).

tff(c_12572,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12561,c_11295])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:46:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.43/2.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.76/2.38  
% 6.76/2.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.76/2.38  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3
% 6.76/2.38  
% 6.76/2.38  %Foreground sorts:
% 6.76/2.38  
% 6.76/2.38  
% 6.76/2.38  %Background operators:
% 6.76/2.38  
% 6.76/2.38  
% 6.76/2.38  %Foreground operators:
% 6.76/2.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.76/2.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.76/2.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.76/2.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.76/2.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.76/2.38  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.76/2.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.76/2.38  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 6.76/2.38  tff('#skF_7', type, '#skF_7': $i).
% 6.76/2.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.76/2.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.76/2.38  tff('#skF_10', type, '#skF_10': $i).
% 6.76/2.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.76/2.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.76/2.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.76/2.38  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 6.76/2.38  tff('#skF_9', type, '#skF_9': $i).
% 6.76/2.38  tff('#skF_8', type, '#skF_8': $i).
% 6.76/2.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.76/2.38  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 6.76/2.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.76/2.38  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.76/2.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.76/2.38  
% 6.89/2.40  tff(f_49, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 6.89/2.40  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.89/2.40  tff(f_69, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.89/2.40  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.89/2.40  tff(f_62, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 6.89/2.40  tff(f_55, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 6.89/2.40  tff(c_11611, plain, (![A_1223, B_1224, C_1225]: (r2_hidden('#skF_3'(A_1223, B_1224, C_1225), B_1224) | r2_hidden('#skF_4'(A_1223, B_1224, C_1225), C_1225) | k2_zfmisc_1(A_1223, B_1224)=C_1225)), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.89/2.40  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.89/2.40  tff(c_10585, plain, (![A_1132, B_1133, C_1134]: (r2_hidden('#skF_2'(A_1132, B_1133, C_1134), A_1132) | r2_hidden('#skF_4'(A_1132, B_1133, C_1134), C_1134) | k2_zfmisc_1(A_1132, B_1133)=C_1134)), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.89/2.40  tff(c_9617, plain, (![A_1010, B_1011, C_1012]: (r2_hidden('#skF_2'(A_1010, B_1011, C_1012), A_1010) | r2_hidden('#skF_4'(A_1010, B_1011, C_1012), C_1012) | k2_zfmisc_1(A_1010, B_1011)=C_1012)), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.89/2.40  tff(c_52, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.89/2.40  tff(c_72, plain, (k1_xboole_0!='#skF_10'), inference(splitLeft, [status(thm)], [c_52])).
% 6.89/2.40  tff(c_7347, plain, (![A_774, B_775, C_776]: (r2_hidden('#skF_3'(A_774, B_775, C_776), B_775) | r2_hidden('#skF_4'(A_774, B_775, C_776), C_776) | k2_zfmisc_1(A_774, B_775)=C_776)), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.89/2.40  tff(c_54, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!=k1_xboole_0 | k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.89/2.40  tff(c_71, plain, (k1_xboole_0!='#skF_9'), inference(splitLeft, [status(thm)], [c_54])).
% 6.89/2.40  tff(c_6488, plain, (![A_695, B_696, C_697]: (r2_hidden('#skF_2'(A_695, B_696, C_697), A_695) | r2_hidden('#skF_4'(A_695, B_696, C_697), C_697) | k2_zfmisc_1(A_695, B_696)=C_697)), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.89/2.40  tff(c_4012, plain, (![A_439, B_440]: (k4_xboole_0(A_439, B_440)=k1_xboole_0 | ~r1_tarski(A_439, B_440))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.89/2.40  tff(c_4022, plain, (![A_443, B_444]: (k4_xboole_0(k4_xboole_0(A_443, B_444), A_443)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_4012])).
% 6.89/2.40  tff(c_46, plain, (![C_51, B_50]: (~r2_hidden(C_51, k4_xboole_0(B_50, k1_tarski(C_51))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.89/2.40  tff(c_4030, plain, (![C_51]: (~r2_hidden(C_51, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4022, c_46])).
% 6.89/2.40  tff(c_3417, plain, (![A_418, B_419, C_420]: (r2_hidden('#skF_2'(A_418, B_419, C_420), A_418) | r2_hidden('#skF_4'(A_418, B_419, C_420), C_420) | k2_zfmisc_1(A_418, B_419)=C_420)), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.89/2.40  tff(c_2288, plain, (![A_300, B_301, C_302]: (r2_hidden('#skF_3'(A_300, B_301, C_302), B_301) | r2_hidden('#skF_4'(A_300, B_301, C_302), C_302) | k2_zfmisc_1(A_300, B_301)=C_302)), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.89/2.40  tff(c_1590, plain, (![A_197, B_198, C_199]: (r2_hidden('#skF_3'(A_197, B_198, C_199), B_198) | r2_hidden('#skF_4'(A_197, B_198, C_199), C_199) | k2_zfmisc_1(A_197, B_198)=C_199)), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.89/2.40  tff(c_1232, plain, (![A_156, B_157, C_158]: (r2_hidden('#skF_2'(A_156, B_157, C_158), A_156) | r2_hidden('#skF_4'(A_156, B_157, C_158), C_158) | k2_zfmisc_1(A_156, B_157)=C_158)), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.89/2.40  tff(c_85, plain, (![A_61, B_62]: (k4_xboole_0(A_61, B_62)=k1_xboole_0 | ~r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.89/2.40  tff(c_94, plain, (![A_63, B_64]: (k4_xboole_0(k4_xboole_0(A_63, B_64), A_63)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_85])).
% 6.89/2.40  tff(c_102, plain, (![C_51]: (~r2_hidden(C_51, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_94, c_46])).
% 6.89/2.40  tff(c_60, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_9', '#skF_10')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.89/2.40  tff(c_113, plain, (k2_zfmisc_1('#skF_9', '#skF_10')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_60])).
% 6.89/2.40  tff(c_215, plain, (![A_87, B_88, C_89, D_90]: (r2_hidden(k4_tarski(A_87, B_88), k2_zfmisc_1(C_89, D_90)) | ~r2_hidden(B_88, D_90) | ~r2_hidden(A_87, C_89))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.89/2.40  tff(c_224, plain, (![A_87, B_88]: (r2_hidden(k4_tarski(A_87, B_88), k1_xboole_0) | ~r2_hidden(B_88, '#skF_10') | ~r2_hidden(A_87, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_113, c_215])).
% 6.89/2.40  tff(c_227, plain, (![B_88, A_87]: (~r2_hidden(B_88, '#skF_10') | ~r2_hidden(A_87, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_102, c_224])).
% 6.89/2.40  tff(c_228, plain, (![A_87]: (~r2_hidden(A_87, '#skF_9'))), inference(splitLeft, [status(thm)], [c_227])).
% 6.89/2.40  tff(c_1318, plain, (![A_159, B_160]: (r2_hidden('#skF_2'(A_159, B_160, '#skF_9'), A_159) | k2_zfmisc_1(A_159, B_160)='#skF_9')), inference(resolution, [status(thm)], [c_1232, c_228])).
% 6.89/2.40  tff(c_1360, plain, (![B_160]: (k2_zfmisc_1('#skF_9', B_160)='#skF_9')), inference(resolution, [status(thm)], [c_1318, c_228])).
% 6.89/2.40  tff(c_1367, plain, (k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1360, c_113])).
% 6.89/2.40  tff(c_1371, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_1367])).
% 6.89/2.40  tff(c_1372, plain, (![B_88]: (~r2_hidden(B_88, '#skF_10'))), inference(splitRight, [status(thm)], [c_227])).
% 6.89/2.40  tff(c_1801, plain, (![A_209, B_210]: (r2_hidden('#skF_3'(A_209, B_210, '#skF_10'), B_210) | k2_zfmisc_1(A_209, B_210)='#skF_10')), inference(resolution, [status(thm)], [c_1590, c_1372])).
% 6.89/2.40  tff(c_1883, plain, (![A_209]: (k2_zfmisc_1(A_209, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_1801, c_1372])).
% 6.89/2.40  tff(c_1889, plain, (k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1883, c_113])).
% 6.89/2.40  tff(c_1891, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_1889])).
% 6.89/2.40  tff(c_1892, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_60])).
% 6.89/2.40  tff(c_1895, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_1892])).
% 6.89/2.40  tff(c_1896, plain, (![C_51]: (~r2_hidden(C_51, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1895, c_102])).
% 6.89/2.40  tff(c_2708, plain, (![A_318, B_319]: (r2_hidden('#skF_3'(A_318, B_319, '#skF_8'), B_319) | k2_zfmisc_1(A_318, B_319)='#skF_8')), inference(resolution, [status(thm)], [c_2288, c_1896])).
% 6.89/2.40  tff(c_2802, plain, (![A_318]: (k2_zfmisc_1(A_318, '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_2708, c_1896])).
% 6.89/2.40  tff(c_58, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!=k1_xboole_0 | k2_zfmisc_1('#skF_9', '#skF_10')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.89/2.40  tff(c_74, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_58])).
% 6.89/2.40  tff(c_1900, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1895, c_74])).
% 6.89/2.40  tff(c_2813, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2802, c_1900])).
% 6.89/2.40  tff(c_2814, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_1892])).
% 6.89/2.40  tff(c_2817, plain, (![C_51]: (~r2_hidden(C_51, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_2814, c_102])).
% 6.89/2.40  tff(c_3957, plain, (![A_437, B_438]: (r2_hidden('#skF_2'(A_437, B_438, '#skF_7'), A_437) | k2_zfmisc_1(A_437, B_438)='#skF_7')), inference(resolution, [status(thm)], [c_3417, c_2817])).
% 6.89/2.40  tff(c_3991, plain, (![B_438]: (k2_zfmisc_1('#skF_7', B_438)='#skF_7')), inference(resolution, [status(thm)], [c_3957, c_2817])).
% 6.89/2.40  tff(c_2821, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_2814, c_74])).
% 6.89/2.40  tff(c_4001, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3991, c_2821])).
% 6.89/2.40  tff(c_4002, plain, (k2_zfmisc_1('#skF_9', '#skF_10')=k1_xboole_0), inference(splitRight, [status(thm)], [c_58])).
% 6.89/2.40  tff(c_4161, plain, (![A_475, B_476, C_477, D_478]: (r2_hidden(k4_tarski(A_475, B_476), k2_zfmisc_1(C_477, D_478)) | ~r2_hidden(B_476, D_478) | ~r2_hidden(A_475, C_477))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.89/2.40  tff(c_4173, plain, (![A_475, B_476]: (r2_hidden(k4_tarski(A_475, B_476), k1_xboole_0) | ~r2_hidden(B_476, '#skF_10') | ~r2_hidden(A_475, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_4002, c_4161])).
% 6.89/2.40  tff(c_4177, plain, (![B_476, A_475]: (~r2_hidden(B_476, '#skF_10') | ~r2_hidden(A_475, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_4030, c_4173])).
% 6.89/2.40  tff(c_6102, plain, (![A_475]: (~r2_hidden(A_475, '#skF_9'))), inference(splitLeft, [status(thm)], [c_4177])).
% 6.89/2.40  tff(c_6800, plain, (![A_710, B_711]: (r2_hidden('#skF_2'(A_710, B_711, '#skF_9'), A_710) | k2_zfmisc_1(A_710, B_711)='#skF_9')), inference(resolution, [status(thm)], [c_6488, c_6102])).
% 6.89/2.40  tff(c_6929, plain, (![B_711]: (k2_zfmisc_1('#skF_9', B_711)='#skF_9')), inference(resolution, [status(thm)], [c_6800, c_6102])).
% 6.89/2.40  tff(c_6940, plain, (k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_6929, c_4002])).
% 6.89/2.40  tff(c_6942, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_6940])).
% 6.89/2.40  tff(c_6943, plain, (![B_476]: (~r2_hidden(B_476, '#skF_10'))), inference(splitRight, [status(thm)], [c_4177])).
% 6.89/2.40  tff(c_7669, plain, (![A_789, B_790]: (r2_hidden('#skF_3'(A_789, B_790, '#skF_10'), B_790) | k2_zfmisc_1(A_789, B_790)='#skF_10')), inference(resolution, [status(thm)], [c_7347, c_6943])).
% 6.89/2.40  tff(c_7803, plain, (![A_789]: (k2_zfmisc_1(A_789, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_7669, c_6943])).
% 6.89/2.40  tff(c_7815, plain, (k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_7803, c_4002])).
% 6.89/2.40  tff(c_7817, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_7815])).
% 6.89/2.40  tff(c_7819, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_52])).
% 6.89/2.40  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.89/2.40  tff(c_9050, plain, (![A_916, B_917]: (k4_xboole_0(A_916, B_917)='#skF_10' | ~r1_tarski(A_916, B_917))), inference(demodulation, [status(thm), theory('equality')], [c_7819, c_4])).
% 6.89/2.40  tff(c_9060, plain, (![A_918, B_919]: (k4_xboole_0(k4_xboole_0(A_918, B_919), A_918)='#skF_10')), inference(resolution, [status(thm)], [c_6, c_9050])).
% 6.89/2.40  tff(c_9068, plain, (![C_51]: (~r2_hidden(C_51, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_9060, c_46])).
% 6.89/2.40  tff(c_9819, plain, (![A_1017, B_1018]: (r2_hidden('#skF_2'(A_1017, B_1018, '#skF_10'), A_1017) | k2_zfmisc_1(A_1017, B_1018)='#skF_10')), inference(resolution, [status(thm)], [c_9617, c_9068])).
% 6.89/2.40  tff(c_9908, plain, (![B_1018]: (k2_zfmisc_1('#skF_10', B_1018)='#skF_10')), inference(resolution, [status(thm)], [c_9819, c_9068])).
% 6.89/2.40  tff(c_8436, plain, (![A_893, B_894, C_895]: (r2_hidden('#skF_3'(A_893, B_894, C_895), B_894) | r2_hidden('#skF_4'(A_893, B_894, C_895), C_895) | k2_zfmisc_1(A_893, B_894)=C_895)), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.89/2.40  tff(c_7818, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_52])).
% 6.89/2.40  tff(c_7825, plain, ('#skF_7'='#skF_10' | '#skF_10'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_7819, c_7819, c_7818])).
% 6.89/2.40  tff(c_7826, plain, ('#skF_10'='#skF_8'), inference(splitLeft, [status(thm)], [c_7825])).
% 6.89/2.40  tff(c_7828, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_7826, c_7819])).
% 6.89/2.40  tff(c_7852, plain, (![A_795, B_796]: (k4_xboole_0(A_795, B_796)='#skF_8' | ~r1_tarski(A_795, B_796))), inference(demodulation, [status(thm), theory('equality')], [c_7828, c_4])).
% 6.89/2.40  tff(c_7857, plain, (![A_797, B_798]: (k4_xboole_0(k4_xboole_0(A_797, B_798), A_797)='#skF_8')), inference(resolution, [status(thm)], [c_6, c_7852])).
% 6.89/2.40  tff(c_7865, plain, (![C_51]: (~r2_hidden(C_51, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_7857, c_46])).
% 6.89/2.40  tff(c_8991, plain, (![A_910, B_911]: (r2_hidden('#skF_3'(A_910, B_911, '#skF_8'), B_911) | k2_zfmisc_1(A_910, B_911)='#skF_8')), inference(resolution, [status(thm)], [c_8436, c_7865])).
% 6.89/2.40  tff(c_9025, plain, (![A_910]: (k2_zfmisc_1(A_910, '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_8991, c_7865])).
% 6.89/2.40  tff(c_50, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!=k1_xboole_0 | k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.89/2.40  tff(c_7838, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_7828, c_7826, c_7828, c_50])).
% 6.89/2.40  tff(c_9035, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9025, c_7838])).
% 6.89/2.40  tff(c_9036, plain, ('#skF_7'='#skF_10'), inference(splitRight, [status(thm)], [c_7825])).
% 6.89/2.40  tff(c_9046, plain, (k2_zfmisc_1('#skF_10', '#skF_8')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_7819, c_9036, c_7819, c_50])).
% 6.89/2.40  tff(c_9918, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9908, c_9046])).
% 6.89/2.40  tff(c_9920, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_54])).
% 6.89/2.40  tff(c_9951, plain, (![A_1025, B_1026]: (k4_xboole_0(A_1025, B_1026)='#skF_9' | ~r1_tarski(A_1025, B_1026))), inference(demodulation, [status(thm), theory('equality')], [c_9920, c_4])).
% 6.89/2.40  tff(c_9960, plain, (![A_1027, B_1028]: (k4_xboole_0(k4_xboole_0(A_1027, B_1028), A_1027)='#skF_9')), inference(resolution, [status(thm)], [c_6, c_9951])).
% 6.89/2.40  tff(c_9968, plain, (![C_51]: (~r2_hidden(C_51, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_9960, c_46])).
% 6.89/2.40  tff(c_11236, plain, (![A_1151, B_1152]: (r2_hidden('#skF_2'(A_1151, B_1152, '#skF_9'), A_1151) | k2_zfmisc_1(A_1151, B_1152)='#skF_9')), inference(resolution, [status(thm)], [c_10585, c_9968])).
% 6.89/2.40  tff(c_11280, plain, (![B_1152]: (k2_zfmisc_1('#skF_9', B_1152)='#skF_9')), inference(resolution, [status(thm)], [c_11236, c_9968])).
% 6.89/2.40  tff(c_56, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.89/2.40  tff(c_9929, plain, ('#skF_9'='#skF_8' | '#skF_7'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_9920, c_9920, c_9920, c_56])).
% 6.89/2.40  tff(c_9930, plain, ('#skF_7'='#skF_9'), inference(splitLeft, [status(thm)], [c_9929])).
% 6.89/2.40  tff(c_9919, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 6.89/2.40  tff(c_9927, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_9920, c_9919])).
% 6.89/2.40  tff(c_9931, plain, (k2_zfmisc_1('#skF_9', '#skF_8')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_9930, c_9927])).
% 6.89/2.40  tff(c_11292, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11280, c_9931])).
% 6.89/2.40  tff(c_11293, plain, ('#skF_9'='#skF_8'), inference(splitRight, [status(thm)], [c_9929])).
% 6.89/2.40  tff(c_11297, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_11293, c_9920])).
% 6.89/2.40  tff(c_11320, plain, (![A_1157, B_1158]: (k4_xboole_0(A_1157, B_1158)='#skF_8' | ~r1_tarski(A_1157, B_1158))), inference(demodulation, [status(thm), theory('equality')], [c_11297, c_4])).
% 6.89/2.40  tff(c_11325, plain, (![A_1159, B_1160]: (k4_xboole_0(k4_xboole_0(A_1159, B_1160), A_1159)='#skF_8')), inference(resolution, [status(thm)], [c_6, c_11320])).
% 6.89/2.40  tff(c_11333, plain, (![C_51]: (~r2_hidden(C_51, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_11325, c_46])).
% 6.89/2.40  tff(c_12522, plain, (![A_1279, B_1280]: (r2_hidden('#skF_3'(A_1279, B_1280, '#skF_8'), B_1280) | k2_zfmisc_1(A_1279, B_1280)='#skF_8')), inference(resolution, [status(thm)], [c_11611, c_11333])).
% 6.89/2.40  tff(c_12561, plain, (![A_1279]: (k2_zfmisc_1(A_1279, '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_12522, c_11333])).
% 6.89/2.40  tff(c_11295, plain, (k2_zfmisc_1('#skF_7', '#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_11293, c_9927])).
% 6.89/2.40  tff(c_12572, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12561, c_11295])).
% 6.89/2.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.89/2.40  
% 6.89/2.40  Inference rules
% 6.89/2.40  ----------------------
% 6.89/2.40  #Ref     : 0
% 6.89/2.40  #Sup     : 2630
% 6.89/2.40  #Fact    : 0
% 6.89/2.40  #Define  : 0
% 6.89/2.40  #Split   : 12
% 6.89/2.40  #Chain   : 0
% 6.89/2.40  #Close   : 0
% 6.89/2.40  
% 6.89/2.40  Ordering : KBO
% 6.89/2.40  
% 6.89/2.40  Simplification rules
% 6.89/2.40  ----------------------
% 6.89/2.40  #Subsume      : 737
% 6.89/2.40  #Demod        : 740
% 6.89/2.40  #Tautology    : 434
% 6.89/2.40  #SimpNegUnit  : 90
% 6.89/2.40  #BackRed      : 170
% 6.89/2.40  
% 6.89/2.40  #Partial instantiations: 0
% 6.89/2.40  #Strategies tried      : 1
% 6.89/2.40  
% 6.89/2.40  Timing (in seconds)
% 6.89/2.40  ----------------------
% 6.89/2.41  Preprocessing        : 0.31
% 6.89/2.41  Parsing              : 0.16
% 6.89/2.41  CNF conversion       : 0.03
% 6.89/2.41  Main loop            : 1.31
% 6.89/2.41  Inferencing          : 0.51
% 6.89/2.41  Reduction            : 0.37
% 6.89/2.41  Demodulation         : 0.22
% 6.89/2.41  BG Simplification    : 0.06
% 6.89/2.41  Subsumption          : 0.23
% 6.89/2.41  Abstraction          : 0.10
% 6.89/2.41  MUC search           : 0.00
% 6.89/2.41  Cooper               : 0.00
% 6.89/2.41  Total                : 1.67
% 6.89/2.41  Index Insertion      : 0.00
% 6.89/2.41  Index Deletion       : 0.00
% 6.89/2.41  Index Matching       : 0.00
% 6.89/2.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
