%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:43 EST 2020

% Result     : Theorem 7.34s
% Output     : CNFRefutation 7.73s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 719 expanded)
%              Number of leaves         :   36 ( 230 expanded)
%              Depth                    :   10
%              Number of atoms          :  213 (1373 expanded)
%              Number of equality atoms :   90 ( 889 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_14478,plain,(
    ! [A_1515,B_1516,C_1517] :
      ( r2_hidden('#skF_4'(A_1515,B_1516,C_1517),B_1516)
      | r2_hidden('#skF_5'(A_1515,B_1516,C_1517),C_1517)
      | k2_zfmisc_1(A_1515,B_1516) = C_1517 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_13084,plain,(
    ! [A_1364,B_1365,C_1366] :
      ( r2_hidden('#skF_4'(A_1364,B_1365,C_1366),B_1365)
      | r2_hidden('#skF_5'(A_1364,B_1365,C_1366),C_1366)
      | k2_zfmisc_1(A_1364,B_1365) = C_1366 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_12062,plain,(
    ! [A_1244,B_1245,C_1246] :
      ( r2_hidden('#skF_3'(A_1244,B_1245,C_1246),A_1244)
      | r2_hidden('#skF_5'(A_1244,B_1245,C_1246),C_1246)
      | k2_zfmisc_1(A_1244,B_1245) = C_1246 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_10715,plain,(
    ! [A_1097,B_1098,C_1099] :
      ( r2_hidden('#skF_4'(A_1097,B_1098,C_1099),B_1098)
      | r2_hidden('#skF_5'(A_1097,B_1098,C_1099),C_1099)
      | k2_zfmisc_1(A_1097,B_1098) = C_1099 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_60,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_80,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_9503,plain,(
    ! [A_958,B_959,C_960] :
      ( r2_hidden('#skF_4'(A_958,B_959,C_960),B_959)
      | r2_hidden('#skF_5'(A_958,B_959,C_960),C_960)
      | k2_zfmisc_1(A_958,B_959) = C_960 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_62,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0
    | k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_79,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_8709,plain,(
    ! [A_893,B_894,C_895] :
      ( r2_hidden('#skF_3'(A_893,B_894,C_895),A_893)
      | r2_hidden('#skF_5'(A_893,B_894,C_895),C_895)
      | k2_zfmisc_1(A_893,B_894) = C_895 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_5156,plain,(
    ! [A_581,B_582,C_583] :
      ( ~ r1_xboole_0(A_581,B_582)
      | ~ r2_hidden(C_583,k3_xboole_0(A_581,B_582)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5160,plain,(
    ! [A_584,C_585] :
      ( ~ r1_xboole_0(A_584,A_584)
      | ~ r2_hidden(C_585,A_584) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_5156])).

tff(c_5164,plain,(
    ! [C_585] : ~ r2_hidden(C_585,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_5160])).

tff(c_4443,plain,(
    ! [A_541,B_542,C_543] :
      ( r2_hidden('#skF_3'(A_541,B_542,C_543),A_541)
      | r2_hidden('#skF_5'(A_541,B_542,C_543),C_543)
      | k2_zfmisc_1(A_541,B_542) = C_543 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3155,plain,(
    ! [A_404,B_405,C_406] :
      ( r2_hidden('#skF_4'(A_404,B_405,C_406),B_405)
      | r2_hidden('#skF_5'(A_404,B_405,C_406),C_406)
      | k2_zfmisc_1(A_404,B_405) = C_406 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2286,plain,(
    ! [A_288,B_289,C_290] :
      ( r2_hidden('#skF_4'(A_288,B_289,C_290),B_289)
      | r2_hidden('#skF_5'(A_288,B_289,C_290),C_290)
      | k2_zfmisc_1(A_288,B_289) = C_290 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_676,plain,(
    ! [A_190,B_191,C_192] :
      ( r2_hidden('#skF_4'(A_190,B_191,C_192),B_191)
      | r2_hidden('#skF_5'(A_190,B_191,C_192),C_192)
      | k2_zfmisc_1(A_190,B_191) = C_192 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_105,plain,(
    ! [A_87,B_88,C_89] :
      ( ~ r1_xboole_0(A_87,B_88)
      | ~ r2_hidden(C_89,k3_xboole_0(A_87,B_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_118,plain,(
    ! [A_93,C_94] :
      ( ~ r1_xboole_0(A_93,A_93)
      | ~ r2_hidden(C_94,A_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_105])).

tff(c_122,plain,(
    ! [C_94] : ~ r2_hidden(C_94,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_118])).

tff(c_68,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k2_zfmisc_1('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_100,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_256,plain,(
    ! [A_125,B_126,C_127,D_128] :
      ( r2_hidden(k4_tarski(A_125,B_126),k2_zfmisc_1(C_127,D_128))
      | ~ r2_hidden(B_126,D_128)
      | ~ r2_hidden(A_125,C_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_265,plain,(
    ! [A_125,B_126] :
      ( r2_hidden(k4_tarski(A_125,B_126),k1_xboole_0)
      | ~ r2_hidden(B_126,'#skF_11')
      | ~ r2_hidden(A_125,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_256])).

tff(c_268,plain,(
    ! [B_126,A_125] :
      ( ~ r2_hidden(B_126,'#skF_11')
      | ~ r2_hidden(A_125,'#skF_10') ) ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_265])).

tff(c_269,plain,(
    ! [A_125] : ~ r2_hidden(A_125,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_268])).

tff(c_948,plain,(
    ! [A_205,C_206] :
      ( r2_hidden('#skF_5'(A_205,'#skF_10',C_206),C_206)
      | k2_zfmisc_1(A_205,'#skF_10') = C_206 ) ),
    inference(resolution,[status(thm)],[c_676,c_269])).

tff(c_1051,plain,(
    ! [A_205] : k2_zfmisc_1(A_205,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_948,c_269])).

tff(c_1052,plain,(
    ! [A_205] : k2_zfmisc_1(A_205,'#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_948,c_122])).

tff(c_1159,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1051,c_1052])).

tff(c_1160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_1159])).

tff(c_1161,plain,(
    ! [B_126] : ~ r2_hidden(B_126,'#skF_11') ),
    inference(splitRight,[status(thm)],[c_268])).

tff(c_2364,plain,(
    ! [A_291,C_292] :
      ( r2_hidden('#skF_5'(A_291,'#skF_11',C_292),C_292)
      | k2_zfmisc_1(A_291,'#skF_11') = C_292 ) ),
    inference(resolution,[status(thm)],[c_2286,c_1161])).

tff(c_2402,plain,(
    ! [A_291] : k2_zfmisc_1(A_291,'#skF_11') = '#skF_11' ),
    inference(resolution,[status(thm)],[c_2364,c_1161])).

tff(c_2411,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2402,c_100])).

tff(c_2415,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2411])).

tff(c_2416,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_2418,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_2416])).

tff(c_2422,plain,(
    ! [A_8] : r1_xboole_0(A_8,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2418,c_8])).

tff(c_2429,plain,(
    ! [A_294,B_295,C_296] :
      ( ~ r1_xboole_0(A_294,B_295)
      | ~ r2_hidden(C_296,k3_xboole_0(A_294,B_295)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2442,plain,(
    ! [A_300,C_301] :
      ( ~ r1_xboole_0(A_300,A_300)
      | ~ r2_hidden(C_301,A_300) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2429])).

tff(c_2446,plain,(
    ! [C_301] : ~ r2_hidden(C_301,'#skF_9') ),
    inference(resolution,[status(thm)],[c_2422,c_2442])).

tff(c_3961,plain,(
    ! [A_447,C_448] :
      ( r2_hidden('#skF_5'(A_447,'#skF_9',C_448),C_448)
      | k2_zfmisc_1(A_447,'#skF_9') = C_448 ) ),
    inference(resolution,[status(thm)],[c_3155,c_2446])).

tff(c_3995,plain,(
    ! [A_447] : k2_zfmisc_1(A_447,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_3961,c_2446])).

tff(c_66,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0
    | k2_zfmisc_1('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_90,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_2419,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2418,c_90])).

tff(c_4009,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3995,c_2419])).

tff(c_4010,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_2416])).

tff(c_4016,plain,(
    ! [A_8] : r1_xboole_0(A_8,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4010,c_8])).

tff(c_4023,plain,(
    ! [A_450,B_451,C_452] :
      ( ~ r1_xboole_0(A_450,B_451)
      | ~ r2_hidden(C_452,k3_xboole_0(A_450,B_451)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4027,plain,(
    ! [A_453,C_454] :
      ( ~ r1_xboole_0(A_453,A_453)
      | ~ r2_hidden(C_454,A_453) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4023])).

tff(c_4031,plain,(
    ! [C_454] : ~ r2_hidden(C_454,'#skF_8') ),
    inference(resolution,[status(thm)],[c_4016,c_4027])).

tff(c_4855,plain,(
    ! [A_574,B_575] :
      ( r2_hidden('#skF_3'(A_574,B_575,'#skF_8'),A_574)
      | k2_zfmisc_1(A_574,B_575) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_4443,c_4031])).

tff(c_4944,plain,(
    ! [B_575] : k2_zfmisc_1('#skF_8',B_575) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_4855,c_4031])).

tff(c_4013,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4010,c_90])).

tff(c_5135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4944,c_4013])).

tff(c_5136,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_5313,plain,(
    ! [A_619,B_620,C_621,D_622] :
      ( r2_hidden(k4_tarski(A_619,B_620),k2_zfmisc_1(C_621,D_622))
      | ~ r2_hidden(B_620,D_622)
      | ~ r2_hidden(A_619,C_621) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_5325,plain,(
    ! [A_619,B_620] :
      ( r2_hidden(k4_tarski(A_619,B_620),k1_xboole_0)
      | ~ r2_hidden(B_620,'#skF_11')
      | ~ r2_hidden(A_619,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5136,c_5313])).

tff(c_5329,plain,(
    ! [B_620,A_619] :
      ( ~ r2_hidden(B_620,'#skF_11')
      | ~ r2_hidden(A_619,'#skF_10') ) ),
    inference(negUnitSimplification,[status(thm)],[c_5164,c_5325])).

tff(c_8250,plain,(
    ! [A_619] : ~ r2_hidden(A_619,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_5329])).

tff(c_8967,plain,(
    ! [A_903,B_904] :
      ( r2_hidden('#skF_3'(A_903,B_904,'#skF_10'),A_903)
      | k2_zfmisc_1(A_903,B_904) = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_8709,c_8250])).

tff(c_9074,plain,(
    ! [B_904] : k2_zfmisc_1('#skF_10',B_904) = '#skF_10' ),
    inference(resolution,[status(thm)],[c_8967,c_8250])).

tff(c_9082,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9074,c_5136])).

tff(c_9085,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_9082])).

tff(c_9086,plain,(
    ! [B_620] : ~ r2_hidden(B_620,'#skF_11') ),
    inference(splitRight,[status(thm)],[c_5329])).

tff(c_9741,plain,(
    ! [A_968,C_969] :
      ( r2_hidden('#skF_5'(A_968,'#skF_11',C_969),C_969)
      | k2_zfmisc_1(A_968,'#skF_11') = C_969 ) ),
    inference(resolution,[status(thm)],[c_9503,c_9086])).

tff(c_9838,plain,(
    ! [A_968] : k2_zfmisc_1(A_968,'#skF_11') = '#skF_11' ),
    inference(resolution,[status(thm)],[c_9741,c_9086])).

tff(c_9847,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9838,c_5136])).

tff(c_9850,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_9847])).

tff(c_9852,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_9851,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_9860,plain,
    ( '#skF_11' = '#skF_8'
    | '#skF_11' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9852,c_9852,c_9851])).

tff(c_9861,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_9860])).

tff(c_9854,plain,(
    ! [A_8] : r1_xboole_0(A_8,'#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9852,c_8])).

tff(c_9862,plain,(
    ! [A_8] : r1_xboole_0(A_8,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9861,c_9854])).

tff(c_9897,plain,(
    ! [A_976,B_977,C_978] :
      ( ~ r1_xboole_0(A_976,B_977)
      | ~ r2_hidden(C_978,k3_xboole_0(A_976,B_977)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_9901,plain,(
    ! [A_979,C_980] :
      ( ~ r1_xboole_0(A_979,A_979)
      | ~ r2_hidden(C_980,A_979) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_9897])).

tff(c_9905,plain,(
    ! [C_980] : ~ r2_hidden(C_980,'#skF_9') ),
    inference(resolution,[status(thm)],[c_9862,c_9901])).

tff(c_11414,plain,(
    ! [A_1131,C_1132] :
      ( r2_hidden('#skF_5'(A_1131,'#skF_9',C_1132),C_1132)
      | k2_zfmisc_1(A_1131,'#skF_9') = C_1132 ) ),
    inference(resolution,[status(thm)],[c_10715,c_9905])).

tff(c_11448,plain,(
    ! [A_1131] : k2_zfmisc_1(A_1131,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_11414,c_9905])).

tff(c_9864,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9861,c_9852])).

tff(c_58,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_9875,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9864,c_9861,c_9864,c_58])).

tff(c_11462,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11448,c_9875])).

tff(c_11463,plain,(
    '#skF_11' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_9860])).

tff(c_11465,plain,(
    ! [A_8] : r1_xboole_0(A_8,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11463,c_9854])).

tff(c_11503,plain,(
    ! [A_1138,B_1139,C_1140] :
      ( ~ r1_xboole_0(A_1138,B_1139)
      | ~ r2_hidden(C_1140,k3_xboole_0(A_1138,B_1139)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_11507,plain,(
    ! [A_1141,C_1142] :
      ( ~ r1_xboole_0(A_1141,A_1141)
      | ~ r2_hidden(C_1142,A_1141) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_11503])).

tff(c_11511,plain,(
    ! [C_1142] : ~ r2_hidden(C_1142,'#skF_8') ),
    inference(resolution,[status(thm)],[c_11465,c_11507])).

tff(c_12335,plain,(
    ! [A_1262,B_1263] :
      ( r2_hidden('#skF_3'(A_1262,B_1263,'#skF_8'),A_1262)
      | k2_zfmisc_1(A_1262,B_1263) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_12062,c_11511])).

tff(c_12424,plain,(
    ! [B_1263] : k2_zfmisc_1('#skF_8',B_1263) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_12335,c_11511])).

tff(c_11467,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11463,c_9852])).

tff(c_11479,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11467,c_11463,c_11467,c_58])).

tff(c_12615,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12424,c_11479])).

tff(c_12617,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_64,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_12629,plain,
    ( '#skF_10' = '#skF_9'
    | '#skF_10' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12617,c_12617,c_12617,c_64])).

tff(c_12630,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_12629])).

tff(c_12618,plain,(
    ! [A_8] : r1_xboole_0(A_8,'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12617,c_8])).

tff(c_12633,plain,(
    ! [A_8] : r1_xboole_0(A_8,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12630,c_12618])).

tff(c_12663,plain,(
    ! [A_1273,B_1274,C_1275] :
      ( ~ r1_xboole_0(A_1273,B_1274)
      | ~ r2_hidden(C_1275,k3_xboole_0(A_1273,B_1274)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12667,plain,(
    ! [A_1276,C_1277] :
      ( ~ r1_xboole_0(A_1276,A_1276)
      | ~ r2_hidden(C_1277,A_1276) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_12663])).

tff(c_12671,plain,(
    ! [C_1277] : ~ r2_hidden(C_1277,'#skF_8') ),
    inference(resolution,[status(thm)],[c_12633,c_12667])).

tff(c_13583,plain,(
    ! [A_1397,C_1398] :
      ( r2_hidden('#skF_5'(A_1397,'#skF_8',C_1398),C_1398)
      | k2_zfmisc_1(A_1397,'#skF_8') = C_1398 ) ),
    inference(resolution,[status(thm)],[c_13084,c_12671])).

tff(c_13672,plain,(
    ! [A_1397] : k2_zfmisc_1(A_1397,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_13583,c_12671])).

tff(c_12900,plain,(
    ! [A_1332,B_1333,D_1334] :
      ( r2_hidden('#skF_6'(A_1332,B_1333,k2_zfmisc_1(A_1332,B_1333),D_1334),A_1332)
      | ~ r2_hidden(D_1334,k2_zfmisc_1(A_1332,B_1333)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_12929,plain,(
    ! [D_1334,B_1333] : ~ r2_hidden(D_1334,k2_zfmisc_1('#skF_8',B_1333)) ),
    inference(resolution,[status(thm)],[c_12900,c_12671])).

tff(c_13667,plain,(
    ! [A_1397,B_1333] : k2_zfmisc_1(A_1397,'#skF_8') = k2_zfmisc_1('#skF_8',B_1333) ),
    inference(resolution,[status(thm)],[c_13583,c_12929])).

tff(c_13856,plain,(
    ! [B_1333] : k2_zfmisc_1('#skF_8',B_1333) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13672,c_13667])).

tff(c_12616,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_12626,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12617,c_12616])).

tff(c_12631,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12630,c_12626])).

tff(c_13872,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13856,c_12631])).

tff(c_13873,plain,(
    '#skF_10' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_12629])).

tff(c_13878,plain,(
    ! [A_8] : r1_xboole_0(A_8,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13873,c_12618])).

tff(c_13908,plain,(
    ! [A_1408,B_1409,C_1410] :
      ( ~ r1_xboole_0(A_1408,B_1409)
      | ~ r2_hidden(C_1410,k3_xboole_0(A_1408,B_1409)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_13914,plain,(
    ! [A_1411,C_1412] :
      ( ~ r1_xboole_0(A_1411,A_1411)
      | ~ r2_hidden(C_1412,A_1411) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_13908])).

tff(c_13918,plain,(
    ! [C_1412] : ~ r2_hidden(C_1412,'#skF_9') ),
    inference(resolution,[status(thm)],[c_13878,c_13914])).

tff(c_14920,plain,(
    ! [A_1535,C_1536] :
      ( r2_hidden('#skF_5'(A_1535,'#skF_9',C_1536),C_1536)
      | k2_zfmisc_1(A_1535,'#skF_9') = C_1536 ) ),
    inference(resolution,[status(thm)],[c_14478,c_13918])).

tff(c_15009,plain,(
    ! [A_1535] : k2_zfmisc_1(A_1535,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_14920,c_13918])).

tff(c_13876,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13873,c_12626])).

tff(c_15023,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15009,c_13876])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:16:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.34/2.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.34/2.57  
% 7.34/2.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.34/2.57  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1
% 7.34/2.57  
% 7.34/2.57  %Foreground sorts:
% 7.34/2.57  
% 7.34/2.57  
% 7.34/2.57  %Background operators:
% 7.34/2.57  
% 7.34/2.57  
% 7.34/2.57  %Foreground operators:
% 7.34/2.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.34/2.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.34/2.57  tff('#skF_11', type, '#skF_11': $i).
% 7.34/2.57  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.34/2.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.34/2.57  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.34/2.57  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 7.34/2.57  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.34/2.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.34/2.57  tff('#skF_10', type, '#skF_10': $i).
% 7.34/2.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.34/2.57  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 7.34/2.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.34/2.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.34/2.57  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.34/2.57  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 7.34/2.57  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 7.34/2.57  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.34/2.57  tff('#skF_9', type, '#skF_9': $i).
% 7.34/2.57  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.34/2.57  tff('#skF_8', type, '#skF_8': $i).
% 7.34/2.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.34/2.57  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.34/2.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.34/2.57  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.34/2.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.34/2.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.34/2.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.34/2.57  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.34/2.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.34/2.57  
% 7.73/2.60  tff(f_71, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 7.73/2.60  tff(f_86, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.73/2.60  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 7.73/2.60  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 7.73/2.60  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 7.73/2.60  tff(f_79, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 7.73/2.60  tff(c_14478, plain, (![A_1515, B_1516, C_1517]: (r2_hidden('#skF_4'(A_1515, B_1516, C_1517), B_1516) | r2_hidden('#skF_5'(A_1515, B_1516, C_1517), C_1517) | k2_zfmisc_1(A_1515, B_1516)=C_1517)), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.73/2.60  tff(c_13084, plain, (![A_1364, B_1365, C_1366]: (r2_hidden('#skF_4'(A_1364, B_1365, C_1366), B_1365) | r2_hidden('#skF_5'(A_1364, B_1365, C_1366), C_1366) | k2_zfmisc_1(A_1364, B_1365)=C_1366)), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.73/2.60  tff(c_12062, plain, (![A_1244, B_1245, C_1246]: (r2_hidden('#skF_3'(A_1244, B_1245, C_1246), A_1244) | r2_hidden('#skF_5'(A_1244, B_1245, C_1246), C_1246) | k2_zfmisc_1(A_1244, B_1245)=C_1246)), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.73/2.60  tff(c_10715, plain, (![A_1097, B_1098, C_1099]: (r2_hidden('#skF_4'(A_1097, B_1098, C_1099), B_1098) | r2_hidden('#skF_5'(A_1097, B_1098, C_1099), C_1099) | k2_zfmisc_1(A_1097, B_1098)=C_1099)), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.73/2.60  tff(c_60, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.73/2.60  tff(c_80, plain, (k1_xboole_0!='#skF_11'), inference(splitLeft, [status(thm)], [c_60])).
% 7.73/2.60  tff(c_9503, plain, (![A_958, B_959, C_960]: (r2_hidden('#skF_4'(A_958, B_959, C_960), B_959) | r2_hidden('#skF_5'(A_958, B_959, C_960), C_960) | k2_zfmisc_1(A_958, B_959)=C_960)), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.73/2.60  tff(c_62, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0 | k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.73/2.60  tff(c_79, plain, (k1_xboole_0!='#skF_10'), inference(splitLeft, [status(thm)], [c_62])).
% 7.73/2.60  tff(c_8709, plain, (![A_893, B_894, C_895]: (r2_hidden('#skF_3'(A_893, B_894, C_895), A_893) | r2_hidden('#skF_5'(A_893, B_894, C_895), C_895) | k2_zfmisc_1(A_893, B_894)=C_895)), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.73/2.60  tff(c_8, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.73/2.60  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.73/2.60  tff(c_5156, plain, (![A_581, B_582, C_583]: (~r1_xboole_0(A_581, B_582) | ~r2_hidden(C_583, k3_xboole_0(A_581, B_582)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.73/2.60  tff(c_5160, plain, (![A_584, C_585]: (~r1_xboole_0(A_584, A_584) | ~r2_hidden(C_585, A_584))), inference(superposition, [status(thm), theory('equality')], [c_2, c_5156])).
% 7.73/2.60  tff(c_5164, plain, (![C_585]: (~r2_hidden(C_585, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_5160])).
% 7.73/2.60  tff(c_4443, plain, (![A_541, B_542, C_543]: (r2_hidden('#skF_3'(A_541, B_542, C_543), A_541) | r2_hidden('#skF_5'(A_541, B_542, C_543), C_543) | k2_zfmisc_1(A_541, B_542)=C_543)), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.73/2.60  tff(c_3155, plain, (![A_404, B_405, C_406]: (r2_hidden('#skF_4'(A_404, B_405, C_406), B_405) | r2_hidden('#skF_5'(A_404, B_405, C_406), C_406) | k2_zfmisc_1(A_404, B_405)=C_406)), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.73/2.60  tff(c_2286, plain, (![A_288, B_289, C_290]: (r2_hidden('#skF_4'(A_288, B_289, C_290), B_289) | r2_hidden('#skF_5'(A_288, B_289, C_290), C_290) | k2_zfmisc_1(A_288, B_289)=C_290)), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.73/2.60  tff(c_676, plain, (![A_190, B_191, C_192]: (r2_hidden('#skF_4'(A_190, B_191, C_192), B_191) | r2_hidden('#skF_5'(A_190, B_191, C_192), C_192) | k2_zfmisc_1(A_190, B_191)=C_192)), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.73/2.60  tff(c_105, plain, (![A_87, B_88, C_89]: (~r1_xboole_0(A_87, B_88) | ~r2_hidden(C_89, k3_xboole_0(A_87, B_88)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.73/2.60  tff(c_118, plain, (![A_93, C_94]: (~r1_xboole_0(A_93, A_93) | ~r2_hidden(C_94, A_93))), inference(superposition, [status(thm), theory('equality')], [c_2, c_105])).
% 7.73/2.60  tff(c_122, plain, (![C_94]: (~r2_hidden(C_94, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_118])).
% 7.73/2.60  tff(c_68, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k2_zfmisc_1('#skF_10', '#skF_11')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.73/2.60  tff(c_100, plain, (k2_zfmisc_1('#skF_10', '#skF_11')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_68])).
% 7.73/2.60  tff(c_256, plain, (![A_125, B_126, C_127, D_128]: (r2_hidden(k4_tarski(A_125, B_126), k2_zfmisc_1(C_127, D_128)) | ~r2_hidden(B_126, D_128) | ~r2_hidden(A_125, C_127))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.73/2.60  tff(c_265, plain, (![A_125, B_126]: (r2_hidden(k4_tarski(A_125, B_126), k1_xboole_0) | ~r2_hidden(B_126, '#skF_11') | ~r2_hidden(A_125, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_100, c_256])).
% 7.73/2.60  tff(c_268, plain, (![B_126, A_125]: (~r2_hidden(B_126, '#skF_11') | ~r2_hidden(A_125, '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_122, c_265])).
% 7.73/2.60  tff(c_269, plain, (![A_125]: (~r2_hidden(A_125, '#skF_10'))), inference(splitLeft, [status(thm)], [c_268])).
% 7.73/2.60  tff(c_948, plain, (![A_205, C_206]: (r2_hidden('#skF_5'(A_205, '#skF_10', C_206), C_206) | k2_zfmisc_1(A_205, '#skF_10')=C_206)), inference(resolution, [status(thm)], [c_676, c_269])).
% 7.73/2.60  tff(c_1051, plain, (![A_205]: (k2_zfmisc_1(A_205, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_948, c_269])).
% 7.73/2.60  tff(c_1052, plain, (![A_205]: (k2_zfmisc_1(A_205, '#skF_10')=k1_xboole_0)), inference(resolution, [status(thm)], [c_948, c_122])).
% 7.73/2.60  tff(c_1159, plain, (k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1051, c_1052])).
% 7.73/2.60  tff(c_1160, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_1159])).
% 7.73/2.60  tff(c_1161, plain, (![B_126]: (~r2_hidden(B_126, '#skF_11'))), inference(splitRight, [status(thm)], [c_268])).
% 7.73/2.60  tff(c_2364, plain, (![A_291, C_292]: (r2_hidden('#skF_5'(A_291, '#skF_11', C_292), C_292) | k2_zfmisc_1(A_291, '#skF_11')=C_292)), inference(resolution, [status(thm)], [c_2286, c_1161])).
% 7.73/2.60  tff(c_2402, plain, (![A_291]: (k2_zfmisc_1(A_291, '#skF_11')='#skF_11')), inference(resolution, [status(thm)], [c_2364, c_1161])).
% 7.73/2.60  tff(c_2411, plain, (k1_xboole_0='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_2402, c_100])).
% 7.73/2.60  tff(c_2415, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_2411])).
% 7.73/2.60  tff(c_2416, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_68])).
% 7.73/2.60  tff(c_2418, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_2416])).
% 7.73/2.60  tff(c_2422, plain, (![A_8]: (r1_xboole_0(A_8, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_2418, c_8])).
% 7.73/2.60  tff(c_2429, plain, (![A_294, B_295, C_296]: (~r1_xboole_0(A_294, B_295) | ~r2_hidden(C_296, k3_xboole_0(A_294, B_295)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.73/2.60  tff(c_2442, plain, (![A_300, C_301]: (~r1_xboole_0(A_300, A_300) | ~r2_hidden(C_301, A_300))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2429])).
% 7.73/2.60  tff(c_2446, plain, (![C_301]: (~r2_hidden(C_301, '#skF_9'))), inference(resolution, [status(thm)], [c_2422, c_2442])).
% 7.73/2.60  tff(c_3961, plain, (![A_447, C_448]: (r2_hidden('#skF_5'(A_447, '#skF_9', C_448), C_448) | k2_zfmisc_1(A_447, '#skF_9')=C_448)), inference(resolution, [status(thm)], [c_3155, c_2446])).
% 7.73/2.60  tff(c_3995, plain, (![A_447]: (k2_zfmisc_1(A_447, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_3961, c_2446])).
% 7.73/2.60  tff(c_66, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0 | k2_zfmisc_1('#skF_10', '#skF_11')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.73/2.60  tff(c_90, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_66])).
% 7.73/2.60  tff(c_2419, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_2418, c_90])).
% 7.73/2.60  tff(c_4009, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3995, c_2419])).
% 7.73/2.60  tff(c_4010, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_2416])).
% 7.73/2.60  tff(c_4016, plain, (![A_8]: (r1_xboole_0(A_8, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_4010, c_8])).
% 7.73/2.60  tff(c_4023, plain, (![A_450, B_451, C_452]: (~r1_xboole_0(A_450, B_451) | ~r2_hidden(C_452, k3_xboole_0(A_450, B_451)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.73/2.60  tff(c_4027, plain, (![A_453, C_454]: (~r1_xboole_0(A_453, A_453) | ~r2_hidden(C_454, A_453))), inference(superposition, [status(thm), theory('equality')], [c_2, c_4023])).
% 7.73/2.60  tff(c_4031, plain, (![C_454]: (~r2_hidden(C_454, '#skF_8'))), inference(resolution, [status(thm)], [c_4016, c_4027])).
% 7.73/2.60  tff(c_4855, plain, (![A_574, B_575]: (r2_hidden('#skF_3'(A_574, B_575, '#skF_8'), A_574) | k2_zfmisc_1(A_574, B_575)='#skF_8')), inference(resolution, [status(thm)], [c_4443, c_4031])).
% 7.73/2.60  tff(c_4944, plain, (![B_575]: (k2_zfmisc_1('#skF_8', B_575)='#skF_8')), inference(resolution, [status(thm)], [c_4855, c_4031])).
% 7.73/2.60  tff(c_4013, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4010, c_90])).
% 7.73/2.60  tff(c_5135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4944, c_4013])).
% 7.73/2.60  tff(c_5136, plain, (k2_zfmisc_1('#skF_10', '#skF_11')=k1_xboole_0), inference(splitRight, [status(thm)], [c_66])).
% 7.73/2.60  tff(c_5313, plain, (![A_619, B_620, C_621, D_622]: (r2_hidden(k4_tarski(A_619, B_620), k2_zfmisc_1(C_621, D_622)) | ~r2_hidden(B_620, D_622) | ~r2_hidden(A_619, C_621))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.73/2.60  tff(c_5325, plain, (![A_619, B_620]: (r2_hidden(k4_tarski(A_619, B_620), k1_xboole_0) | ~r2_hidden(B_620, '#skF_11') | ~r2_hidden(A_619, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_5136, c_5313])).
% 7.73/2.60  tff(c_5329, plain, (![B_620, A_619]: (~r2_hidden(B_620, '#skF_11') | ~r2_hidden(A_619, '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_5164, c_5325])).
% 7.73/2.60  tff(c_8250, plain, (![A_619]: (~r2_hidden(A_619, '#skF_10'))), inference(splitLeft, [status(thm)], [c_5329])).
% 7.73/2.60  tff(c_8967, plain, (![A_903, B_904]: (r2_hidden('#skF_3'(A_903, B_904, '#skF_10'), A_903) | k2_zfmisc_1(A_903, B_904)='#skF_10')), inference(resolution, [status(thm)], [c_8709, c_8250])).
% 7.73/2.60  tff(c_9074, plain, (![B_904]: (k2_zfmisc_1('#skF_10', B_904)='#skF_10')), inference(resolution, [status(thm)], [c_8967, c_8250])).
% 7.73/2.60  tff(c_9082, plain, (k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_9074, c_5136])).
% 7.73/2.60  tff(c_9085, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_9082])).
% 7.73/2.60  tff(c_9086, plain, (![B_620]: (~r2_hidden(B_620, '#skF_11'))), inference(splitRight, [status(thm)], [c_5329])).
% 7.73/2.60  tff(c_9741, plain, (![A_968, C_969]: (r2_hidden('#skF_5'(A_968, '#skF_11', C_969), C_969) | k2_zfmisc_1(A_968, '#skF_11')=C_969)), inference(resolution, [status(thm)], [c_9503, c_9086])).
% 7.73/2.60  tff(c_9838, plain, (![A_968]: (k2_zfmisc_1(A_968, '#skF_11')='#skF_11')), inference(resolution, [status(thm)], [c_9741, c_9086])).
% 7.73/2.60  tff(c_9847, plain, (k1_xboole_0='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_9838, c_5136])).
% 7.73/2.60  tff(c_9850, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_9847])).
% 7.73/2.60  tff(c_9852, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_60])).
% 7.73/2.60  tff(c_9851, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_60])).
% 7.73/2.60  tff(c_9860, plain, ('#skF_11'='#skF_8' | '#skF_11'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_9852, c_9852, c_9851])).
% 7.73/2.60  tff(c_9861, plain, ('#skF_11'='#skF_9'), inference(splitLeft, [status(thm)], [c_9860])).
% 7.73/2.60  tff(c_9854, plain, (![A_8]: (r1_xboole_0(A_8, '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_9852, c_8])).
% 7.73/2.60  tff(c_9862, plain, (![A_8]: (r1_xboole_0(A_8, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_9861, c_9854])).
% 7.73/2.60  tff(c_9897, plain, (![A_976, B_977, C_978]: (~r1_xboole_0(A_976, B_977) | ~r2_hidden(C_978, k3_xboole_0(A_976, B_977)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.73/2.60  tff(c_9901, plain, (![A_979, C_980]: (~r1_xboole_0(A_979, A_979) | ~r2_hidden(C_980, A_979))), inference(superposition, [status(thm), theory('equality')], [c_2, c_9897])).
% 7.73/2.60  tff(c_9905, plain, (![C_980]: (~r2_hidden(C_980, '#skF_9'))), inference(resolution, [status(thm)], [c_9862, c_9901])).
% 7.73/2.60  tff(c_11414, plain, (![A_1131, C_1132]: (r2_hidden('#skF_5'(A_1131, '#skF_9', C_1132), C_1132) | k2_zfmisc_1(A_1131, '#skF_9')=C_1132)), inference(resolution, [status(thm)], [c_10715, c_9905])).
% 7.73/2.60  tff(c_11448, plain, (![A_1131]: (k2_zfmisc_1(A_1131, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_11414, c_9905])).
% 7.73/2.60  tff(c_9864, plain, (k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_9861, c_9852])).
% 7.73/2.60  tff(c_58, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0 | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.73/2.60  tff(c_9875, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_9864, c_9861, c_9864, c_58])).
% 7.73/2.60  tff(c_11462, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11448, c_9875])).
% 7.73/2.60  tff(c_11463, plain, ('#skF_11'='#skF_8'), inference(splitRight, [status(thm)], [c_9860])).
% 7.73/2.60  tff(c_11465, plain, (![A_8]: (r1_xboole_0(A_8, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_11463, c_9854])).
% 7.73/2.60  tff(c_11503, plain, (![A_1138, B_1139, C_1140]: (~r1_xboole_0(A_1138, B_1139) | ~r2_hidden(C_1140, k3_xboole_0(A_1138, B_1139)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.73/2.60  tff(c_11507, plain, (![A_1141, C_1142]: (~r1_xboole_0(A_1141, A_1141) | ~r2_hidden(C_1142, A_1141))), inference(superposition, [status(thm), theory('equality')], [c_2, c_11503])).
% 7.73/2.60  tff(c_11511, plain, (![C_1142]: (~r2_hidden(C_1142, '#skF_8'))), inference(resolution, [status(thm)], [c_11465, c_11507])).
% 7.73/2.60  tff(c_12335, plain, (![A_1262, B_1263]: (r2_hidden('#skF_3'(A_1262, B_1263, '#skF_8'), A_1262) | k2_zfmisc_1(A_1262, B_1263)='#skF_8')), inference(resolution, [status(thm)], [c_12062, c_11511])).
% 7.73/2.60  tff(c_12424, plain, (![B_1263]: (k2_zfmisc_1('#skF_8', B_1263)='#skF_8')), inference(resolution, [status(thm)], [c_12335, c_11511])).
% 7.73/2.60  tff(c_11467, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_11463, c_9852])).
% 7.73/2.60  tff(c_11479, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_11467, c_11463, c_11467, c_58])).
% 7.73/2.60  tff(c_12615, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12424, c_11479])).
% 7.73/2.60  tff(c_12617, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_62])).
% 7.73/2.60  tff(c_64, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.73/2.60  tff(c_12629, plain, ('#skF_10'='#skF_9' | '#skF_10'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_12617, c_12617, c_12617, c_64])).
% 7.73/2.60  tff(c_12630, plain, ('#skF_10'='#skF_8'), inference(splitLeft, [status(thm)], [c_12629])).
% 7.73/2.60  tff(c_12618, plain, (![A_8]: (r1_xboole_0(A_8, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_12617, c_8])).
% 7.73/2.60  tff(c_12633, plain, (![A_8]: (r1_xboole_0(A_8, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_12630, c_12618])).
% 7.73/2.60  tff(c_12663, plain, (![A_1273, B_1274, C_1275]: (~r1_xboole_0(A_1273, B_1274) | ~r2_hidden(C_1275, k3_xboole_0(A_1273, B_1274)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.73/2.60  tff(c_12667, plain, (![A_1276, C_1277]: (~r1_xboole_0(A_1276, A_1276) | ~r2_hidden(C_1277, A_1276))), inference(superposition, [status(thm), theory('equality')], [c_2, c_12663])).
% 7.73/2.60  tff(c_12671, plain, (![C_1277]: (~r2_hidden(C_1277, '#skF_8'))), inference(resolution, [status(thm)], [c_12633, c_12667])).
% 7.73/2.60  tff(c_13583, plain, (![A_1397, C_1398]: (r2_hidden('#skF_5'(A_1397, '#skF_8', C_1398), C_1398) | k2_zfmisc_1(A_1397, '#skF_8')=C_1398)), inference(resolution, [status(thm)], [c_13084, c_12671])).
% 7.73/2.60  tff(c_13672, plain, (![A_1397]: (k2_zfmisc_1(A_1397, '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_13583, c_12671])).
% 7.73/2.60  tff(c_12900, plain, (![A_1332, B_1333, D_1334]: (r2_hidden('#skF_6'(A_1332, B_1333, k2_zfmisc_1(A_1332, B_1333), D_1334), A_1332) | ~r2_hidden(D_1334, k2_zfmisc_1(A_1332, B_1333)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.73/2.60  tff(c_12929, plain, (![D_1334, B_1333]: (~r2_hidden(D_1334, k2_zfmisc_1('#skF_8', B_1333)))), inference(resolution, [status(thm)], [c_12900, c_12671])).
% 7.73/2.60  tff(c_13667, plain, (![A_1397, B_1333]: (k2_zfmisc_1(A_1397, '#skF_8')=k2_zfmisc_1('#skF_8', B_1333))), inference(resolution, [status(thm)], [c_13583, c_12929])).
% 7.73/2.60  tff(c_13856, plain, (![B_1333]: (k2_zfmisc_1('#skF_8', B_1333)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_13672, c_13667])).
% 7.73/2.60  tff(c_12616, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_62])).
% 7.73/2.60  tff(c_12626, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_12617, c_12616])).
% 7.73/2.60  tff(c_12631, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_12630, c_12626])).
% 7.73/2.60  tff(c_13872, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13856, c_12631])).
% 7.73/2.60  tff(c_13873, plain, ('#skF_10'='#skF_9'), inference(splitRight, [status(thm)], [c_12629])).
% 7.73/2.60  tff(c_13878, plain, (![A_8]: (r1_xboole_0(A_8, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_13873, c_12618])).
% 7.73/2.60  tff(c_13908, plain, (![A_1408, B_1409, C_1410]: (~r1_xboole_0(A_1408, B_1409) | ~r2_hidden(C_1410, k3_xboole_0(A_1408, B_1409)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.73/2.60  tff(c_13914, plain, (![A_1411, C_1412]: (~r1_xboole_0(A_1411, A_1411) | ~r2_hidden(C_1412, A_1411))), inference(superposition, [status(thm), theory('equality')], [c_2, c_13908])).
% 7.73/2.60  tff(c_13918, plain, (![C_1412]: (~r2_hidden(C_1412, '#skF_9'))), inference(resolution, [status(thm)], [c_13878, c_13914])).
% 7.73/2.60  tff(c_14920, plain, (![A_1535, C_1536]: (r2_hidden('#skF_5'(A_1535, '#skF_9', C_1536), C_1536) | k2_zfmisc_1(A_1535, '#skF_9')=C_1536)), inference(resolution, [status(thm)], [c_14478, c_13918])).
% 7.73/2.60  tff(c_15009, plain, (![A_1535]: (k2_zfmisc_1(A_1535, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_14920, c_13918])).
% 7.73/2.60  tff(c_13876, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_13873, c_12626])).
% 7.73/2.60  tff(c_15023, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15009, c_13876])).
% 7.73/2.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.73/2.60  
% 7.73/2.60  Inference rules
% 7.73/2.60  ----------------------
% 7.73/2.60  #Ref     : 0
% 7.73/2.60  #Sup     : 3101
% 7.73/2.60  #Fact    : 0
% 7.73/2.60  #Define  : 0
% 7.73/2.60  #Split   : 12
% 7.73/2.60  #Chain   : 0
% 7.73/2.60  #Close   : 0
% 7.73/2.60  
% 7.73/2.60  Ordering : KBO
% 7.73/2.60  
% 7.73/2.60  Simplification rules
% 7.73/2.60  ----------------------
% 7.73/2.60  #Subsume      : 940
% 7.73/2.60  #Demod        : 750
% 7.73/2.60  #Tautology    : 444
% 7.73/2.60  #SimpNegUnit  : 66
% 7.73/2.60  #BackRed      : 180
% 7.73/2.60  
% 7.73/2.60  #Partial instantiations: 0
% 7.73/2.60  #Strategies tried      : 1
% 7.73/2.60  
% 7.73/2.60  Timing (in seconds)
% 7.73/2.60  ----------------------
% 7.73/2.60  Preprocessing        : 0.35
% 7.73/2.60  Parsing              : 0.18
% 7.73/2.60  CNF conversion       : 0.03
% 7.73/2.60  Main loop            : 1.46
% 7.73/2.60  Inferencing          : 0.59
% 7.73/2.60  Reduction            : 0.41
% 7.73/2.60  Demodulation         : 0.25
% 7.73/2.60  BG Simplification    : 0.07
% 7.73/2.60  Subsumption          : 0.26
% 7.73/2.60  Abstraction          : 0.08
% 7.73/2.60  MUC search           : 0.00
% 7.73/2.60  Cooper               : 0.00
% 7.73/2.60  Total                : 1.86
% 7.73/2.60  Index Insertion      : 0.00
% 7.73/2.60  Index Deletion       : 0.00
% 7.73/2.60  Index Matching       : 0.00
% 7.73/2.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
