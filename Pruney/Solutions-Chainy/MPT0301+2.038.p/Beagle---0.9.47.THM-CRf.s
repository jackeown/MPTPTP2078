%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:45 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 477 expanded)
%              Number of leaves         :   32 ( 151 expanded)
%              Depth                    :    9
%              Number of atoms          :  160 ( 916 expanded)
%              Number of equality atoms :   75 ( 757 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_xboole_0 > #skF_11 > #skF_1 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_35,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(c_52,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_54,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0
    | k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_4,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_80,plain,(
    ! [A_76,C_77,B_78] :
      ( ~ r2_hidden(A_76,C_77)
      | ~ r1_xboole_0(k2_tarski(A_76,B_78),C_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_85,plain,(
    ! [A_76] : ~ r2_hidden(A_76,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_80])).

tff(c_60,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k2_zfmisc_1('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_74,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_128,plain,(
    ! [A_100,B_101,C_102,D_103] :
      ( r2_hidden(k4_tarski(A_100,B_101),k2_zfmisc_1(C_102,D_103))
      | ~ r2_hidden(B_101,D_103)
      | ~ r2_hidden(A_100,C_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_137,plain,(
    ! [A_100,B_101] :
      ( r2_hidden(k4_tarski(A_100,B_101),k1_xboole_0)
      | ~ r2_hidden(B_101,'#skF_11')
      | ~ r2_hidden(A_100,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_128])).

tff(c_140,plain,(
    ! [B_101,A_100] :
      ( ~ r2_hidden(B_101,'#skF_11')
      | ~ r2_hidden(A_100,'#skF_10') ) ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_137])).

tff(c_142,plain,(
    ! [A_104] : ~ r2_hidden(A_104,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_146,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_2,c_142])).

tff(c_150,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_146])).

tff(c_152,plain,(
    ! [B_105] : ~ r2_hidden(B_105,'#skF_11') ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_156,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_2,c_152])).

tff(c_160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_156])).

tff(c_161,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_163,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_161])).

tff(c_165,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | A_1 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_2])).

tff(c_275,plain,(
    ! [A_142,B_143,D_144] :
      ( r2_hidden('#skF_7'(A_142,B_143,k2_zfmisc_1(A_142,B_143),D_144),B_143)
      | ~ r2_hidden(D_144,k2_zfmisc_1(A_142,B_143)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_167,plain,(
    ! [A_3] : r1_xboole_0(A_3,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_4])).

tff(c_177,plain,(
    ! [A_108,C_109,B_110] :
      ( ~ r2_hidden(A_108,C_109)
      | ~ r1_xboole_0(k2_tarski(A_108,B_110),C_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_182,plain,(
    ! [A_108] : ~ r2_hidden(A_108,'#skF_9') ),
    inference(resolution,[status(thm)],[c_167,c_177])).

tff(c_285,plain,(
    ! [D_145,A_146] : ~ r2_hidden(D_145,k2_zfmisc_1(A_146,'#skF_9')) ),
    inference(resolution,[status(thm)],[c_275,c_182])).

tff(c_308,plain,(
    ! [A_146] : k2_zfmisc_1(A_146,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_165,c_285])).

tff(c_162,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_173,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_162])).

tff(c_58,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0
    | k2_zfmisc_1('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_174,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != '#skF_9'
    | k2_zfmisc_1('#skF_10','#skF_11') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_163,c_58])).

tff(c_175,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_174])).

tff(c_321,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_175])).

tff(c_322,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_161])).

tff(c_428,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_162])).

tff(c_325,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | A_1 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_2])).

tff(c_389,plain,(
    ! [A_183,B_184,D_185] :
      ( r2_hidden('#skF_6'(A_183,B_184,k2_zfmisc_1(A_183,B_184),D_185),A_183)
      | ~ r2_hidden(D_185,k2_zfmisc_1(A_183,B_184)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_327,plain,(
    ! [A_3] : r1_xboole_0(A_3,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_4])).

tff(c_338,plain,(
    ! [A_155,C_156,B_157] :
      ( ~ r2_hidden(A_155,C_156)
      | ~ r1_xboole_0(k2_tarski(A_155,B_157),C_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_343,plain,(
    ! [A_155] : ~ r2_hidden(A_155,'#skF_8') ),
    inference(resolution,[status(thm)],[c_327,c_338])).

tff(c_401,plain,(
    ! [D_189,B_190] : ~ r2_hidden(D_189,k2_zfmisc_1('#skF_8',B_190)) ),
    inference(resolution,[status(thm)],[c_389,c_343])).

tff(c_421,plain,(
    ! [B_190] : k2_zfmisc_1('#skF_8',B_190) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_325,c_401])).

tff(c_333,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != '#skF_8'
    | k2_zfmisc_1('#skF_10','#skF_11') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_322,c_58])).

tff(c_334,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_333])).

tff(c_425,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_334])).

tff(c_426,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_333])).

tff(c_434,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_428,c_426])).

tff(c_436,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_435,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_445,plain,
    ( '#skF_11' = '#skF_8'
    | '#skF_11' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_436,c_435])).

tff(c_446,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_445])).

tff(c_437,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | A_1 = '#skF_11' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_2])).

tff(c_463,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | A_1 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_446,c_437])).

tff(c_533,plain,(
    ! [A_228,B_229,D_230] :
      ( r2_hidden('#skF_7'(A_228,B_229,k2_zfmisc_1(A_228,B_229),D_230),B_229)
      | ~ r2_hidden(D_230,k2_zfmisc_1(A_228,B_229)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_439,plain,(
    ! [A_3] : r1_xboole_0(A_3,'#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_4])).

tff(c_447,plain,(
    ! [A_3] : r1_xboole_0(A_3,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_446,c_439])).

tff(c_476,plain,(
    ! [A_197,C_198,B_199] :
      ( ~ r2_hidden(A_197,C_198)
      | ~ r1_xboole_0(k2_tarski(A_197,B_199),C_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_481,plain,(
    ! [A_197] : ~ r2_hidden(A_197,'#skF_9') ),
    inference(resolution,[status(thm)],[c_447,c_476])).

tff(c_588,plain,(
    ! [D_234,A_235] : ~ r2_hidden(D_234,k2_zfmisc_1(A_235,'#skF_9')) ),
    inference(resolution,[status(thm)],[c_533,c_481])).

tff(c_611,plain,(
    ! [A_235] : k2_zfmisc_1(A_235,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_463,c_588])).

tff(c_449,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_446,c_436])).

tff(c_50,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_462,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_449,c_446,c_449,c_50])).

tff(c_615,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_611,c_462])).

tff(c_616,plain,(
    '#skF_11' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_445])).

tff(c_635,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | A_1 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_437])).

tff(c_700,plain,(
    ! [A_268,B_269,D_270] :
      ( r2_hidden('#skF_6'(A_268,B_269,k2_zfmisc_1(A_268,B_269),D_270),A_268)
      | ~ r2_hidden(D_270,k2_zfmisc_1(A_268,B_269)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_618,plain,(
    ! [A_3] : r1_xboole_0(A_3,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_439])).

tff(c_648,plain,(
    ! [A_240,C_241,B_242] :
      ( ~ r2_hidden(A_240,C_241)
      | ~ r1_xboole_0(k2_tarski(A_240,B_242),C_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_653,plain,(
    ! [A_240] : ~ r2_hidden(A_240,'#skF_8') ),
    inference(resolution,[status(thm)],[c_618,c_648])).

tff(c_706,plain,(
    ! [D_271,B_272] : ~ r2_hidden(D_271,k2_zfmisc_1('#skF_8',B_272)) ),
    inference(resolution,[status(thm)],[c_700,c_653])).

tff(c_721,plain,(
    ! [B_272] : k2_zfmisc_1('#skF_8',B_272) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_635,c_706])).

tff(c_620,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_436])).

tff(c_632,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_620,c_616,c_620,c_50])).

tff(c_736,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_721,c_632])).

tff(c_738,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_56,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_746,plain,
    ( '#skF_10' = '#skF_9'
    | '#skF_10' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_738,c_738,c_738,c_56])).

tff(c_747,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_746])).

tff(c_749,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_747,c_738])).

tff(c_760,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | A_1 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_749,c_2])).

tff(c_832,plain,(
    ! [A_312,B_313,D_314] :
      ( r2_hidden('#skF_6'(A_312,B_313,k2_zfmisc_1(A_312,B_313),D_314),A_312)
      | ~ r2_hidden(D_314,k2_zfmisc_1(A_312,B_313)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_739,plain,(
    ! [A_3] : r1_xboole_0(A_3,'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_738,c_4])).

tff(c_748,plain,(
    ! [A_3] : r1_xboole_0(A_3,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_747,c_739])).

tff(c_775,plain,(
    ! [A_281,C_282,B_283] :
      ( ~ r2_hidden(A_281,C_282)
      | ~ r1_xboole_0(k2_tarski(A_281,B_283),C_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_780,plain,(
    ! [A_281] : ~ r2_hidden(A_281,'#skF_8') ),
    inference(resolution,[status(thm)],[c_748,c_775])).

tff(c_887,plain,(
    ! [D_318,B_319] : ~ r2_hidden(D_318,k2_zfmisc_1('#skF_8',B_319)) ),
    inference(resolution,[status(thm)],[c_832,c_780])).

tff(c_910,plain,(
    ! [B_319] : k2_zfmisc_1('#skF_8',B_319) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_760,c_887])).

tff(c_737,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_759,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_749,c_737])).

tff(c_914,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_910,c_759])).

tff(c_915,plain,(
    '#skF_10' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_746])).

tff(c_918,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_915,c_738])).

tff(c_933,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | A_1 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_918,c_2])).

tff(c_1020,plain,(
    ! [A_357,B_358,D_359] :
      ( r2_hidden('#skF_7'(A_357,B_358,k2_zfmisc_1(A_357,B_358),D_359),B_358)
      | ~ r2_hidden(D_359,k2_zfmisc_1(A_357,B_358)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_917,plain,(
    ! [A_3] : r1_xboole_0(A_3,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_915,c_739])).

tff(c_946,plain,(
    ! [A_324,C_325,B_326] :
      ( ~ r2_hidden(A_324,C_325)
      | ~ r1_xboole_0(k2_tarski(A_324,B_326),C_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_951,plain,(
    ! [A_324] : ~ r2_hidden(A_324,'#skF_9') ),
    inference(resolution,[status(thm)],[c_917,c_946])).

tff(c_1059,plain,(
    ! [D_361,A_362] : ~ r2_hidden(D_361,k2_zfmisc_1(A_362,'#skF_9')) ),
    inference(resolution,[status(thm)],[c_1020,c_951])).

tff(c_1082,plain,(
    ! [A_362] : k2_zfmisc_1(A_362,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_933,c_1059])).

tff(c_929,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_918,c_737])).

tff(c_1086,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1082,c_929])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:14:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.47  
% 2.85/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.47  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_xboole_0 > #skF_11 > #skF_1 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3
% 2.85/1.47  
% 2.85/1.47  %Foreground sorts:
% 2.85/1.47  
% 2.85/1.47  
% 2.85/1.47  %Background operators:
% 2.85/1.47  
% 2.85/1.47  
% 2.85/1.47  %Foreground operators:
% 2.85/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.85/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.85/1.47  tff('#skF_11', type, '#skF_11': $i).
% 2.85/1.47  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.85/1.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.85/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.85/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.85/1.47  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.85/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.85/1.47  tff('#skF_10', type, '#skF_10': $i).
% 2.85/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.85/1.47  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.85/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.85/1.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.85/1.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.85/1.47  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 2.85/1.47  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 2.85/1.47  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.85/1.47  tff('#skF_9', type, '#skF_9': $i).
% 2.85/1.47  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.85/1.47  tff('#skF_8', type, '#skF_8': $i).
% 2.85/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.85/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.85/1.47  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.85/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.85/1.47  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.85/1.47  
% 2.99/1.49  tff(f_77, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.99/1.49  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.99/1.49  tff(f_35, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.99/1.49  tff(f_70, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.99/1.49  tff(f_65, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.99/1.49  tff(f_59, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 2.99/1.49  tff(c_52, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.99/1.49  tff(c_64, plain, (k1_xboole_0!='#skF_11'), inference(splitLeft, [status(thm)], [c_52])).
% 2.99/1.49  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.99/1.49  tff(c_54, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0 | k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.99/1.49  tff(c_62, plain, (k1_xboole_0!='#skF_10'), inference(splitLeft, [status(thm)], [c_54])).
% 2.99/1.49  tff(c_4, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.99/1.49  tff(c_80, plain, (![A_76, C_77, B_78]: (~r2_hidden(A_76, C_77) | ~r1_xboole_0(k2_tarski(A_76, B_78), C_77))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.99/1.49  tff(c_85, plain, (![A_76]: (~r2_hidden(A_76, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_80])).
% 2.99/1.49  tff(c_60, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k2_zfmisc_1('#skF_10', '#skF_11')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.99/1.49  tff(c_74, plain, (k2_zfmisc_1('#skF_10', '#skF_11')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_60])).
% 2.99/1.49  tff(c_128, plain, (![A_100, B_101, C_102, D_103]: (r2_hidden(k4_tarski(A_100, B_101), k2_zfmisc_1(C_102, D_103)) | ~r2_hidden(B_101, D_103) | ~r2_hidden(A_100, C_102))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.99/1.49  tff(c_137, plain, (![A_100, B_101]: (r2_hidden(k4_tarski(A_100, B_101), k1_xboole_0) | ~r2_hidden(B_101, '#skF_11') | ~r2_hidden(A_100, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_128])).
% 2.99/1.49  tff(c_140, plain, (![B_101, A_100]: (~r2_hidden(B_101, '#skF_11') | ~r2_hidden(A_100, '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_85, c_137])).
% 2.99/1.49  tff(c_142, plain, (![A_104]: (~r2_hidden(A_104, '#skF_10'))), inference(splitLeft, [status(thm)], [c_140])).
% 2.99/1.49  tff(c_146, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_2, c_142])).
% 2.99/1.49  tff(c_150, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_146])).
% 2.99/1.49  tff(c_152, plain, (![B_105]: (~r2_hidden(B_105, '#skF_11'))), inference(splitRight, [status(thm)], [c_140])).
% 2.99/1.49  tff(c_156, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_2, c_152])).
% 2.99/1.49  tff(c_160, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_156])).
% 2.99/1.49  tff(c_161, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_60])).
% 2.99/1.49  tff(c_163, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_161])).
% 2.99/1.49  tff(c_165, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | A_1='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_163, c_2])).
% 2.99/1.49  tff(c_275, plain, (![A_142, B_143, D_144]: (r2_hidden('#skF_7'(A_142, B_143, k2_zfmisc_1(A_142, B_143), D_144), B_143) | ~r2_hidden(D_144, k2_zfmisc_1(A_142, B_143)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.99/1.49  tff(c_167, plain, (![A_3]: (r1_xboole_0(A_3, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_4])).
% 2.99/1.49  tff(c_177, plain, (![A_108, C_109, B_110]: (~r2_hidden(A_108, C_109) | ~r1_xboole_0(k2_tarski(A_108, B_110), C_109))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.99/1.49  tff(c_182, plain, (![A_108]: (~r2_hidden(A_108, '#skF_9'))), inference(resolution, [status(thm)], [c_167, c_177])).
% 2.99/1.49  tff(c_285, plain, (![D_145, A_146]: (~r2_hidden(D_145, k2_zfmisc_1(A_146, '#skF_9')))), inference(resolution, [status(thm)], [c_275, c_182])).
% 2.99/1.49  tff(c_308, plain, (![A_146]: (k2_zfmisc_1(A_146, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_165, c_285])).
% 2.99/1.49  tff(c_162, plain, (k2_zfmisc_1('#skF_10', '#skF_11')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_60])).
% 2.99/1.49  tff(c_173, plain, (k2_zfmisc_1('#skF_10', '#skF_11')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_163, c_162])).
% 2.99/1.49  tff(c_58, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0 | k2_zfmisc_1('#skF_10', '#skF_11')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.99/1.49  tff(c_174, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_9' | k2_zfmisc_1('#skF_10', '#skF_11')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_163, c_163, c_58])).
% 2.99/1.49  tff(c_175, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_173, c_174])).
% 2.99/1.49  tff(c_321, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_308, c_175])).
% 2.99/1.49  tff(c_322, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_161])).
% 2.99/1.49  tff(c_428, plain, (k2_zfmisc_1('#skF_10', '#skF_11')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_322, c_162])).
% 2.99/1.49  tff(c_325, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | A_1='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_322, c_2])).
% 2.99/1.49  tff(c_389, plain, (![A_183, B_184, D_185]: (r2_hidden('#skF_6'(A_183, B_184, k2_zfmisc_1(A_183, B_184), D_185), A_183) | ~r2_hidden(D_185, k2_zfmisc_1(A_183, B_184)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.99/1.49  tff(c_327, plain, (![A_3]: (r1_xboole_0(A_3, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_322, c_4])).
% 2.99/1.49  tff(c_338, plain, (![A_155, C_156, B_157]: (~r2_hidden(A_155, C_156) | ~r1_xboole_0(k2_tarski(A_155, B_157), C_156))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.99/1.49  tff(c_343, plain, (![A_155]: (~r2_hidden(A_155, '#skF_8'))), inference(resolution, [status(thm)], [c_327, c_338])).
% 2.99/1.49  tff(c_401, plain, (![D_189, B_190]: (~r2_hidden(D_189, k2_zfmisc_1('#skF_8', B_190)))), inference(resolution, [status(thm)], [c_389, c_343])).
% 2.99/1.49  tff(c_421, plain, (![B_190]: (k2_zfmisc_1('#skF_8', B_190)='#skF_8')), inference(resolution, [status(thm)], [c_325, c_401])).
% 2.99/1.49  tff(c_333, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_8' | k2_zfmisc_1('#skF_10', '#skF_11')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_322, c_322, c_58])).
% 2.99/1.49  tff(c_334, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_8'), inference(splitLeft, [status(thm)], [c_333])).
% 2.99/1.49  tff(c_425, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_421, c_334])).
% 2.99/1.49  tff(c_426, plain, (k2_zfmisc_1('#skF_10', '#skF_11')='#skF_8'), inference(splitRight, [status(thm)], [c_333])).
% 2.99/1.49  tff(c_434, plain, $false, inference(negUnitSimplification, [status(thm)], [c_428, c_426])).
% 2.99/1.49  tff(c_436, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_52])).
% 2.99/1.49  tff(c_435, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_52])).
% 2.99/1.49  tff(c_445, plain, ('#skF_11'='#skF_8' | '#skF_11'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_436, c_436, c_435])).
% 2.99/1.49  tff(c_446, plain, ('#skF_11'='#skF_9'), inference(splitLeft, [status(thm)], [c_445])).
% 2.99/1.49  tff(c_437, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | A_1='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_436, c_2])).
% 2.99/1.49  tff(c_463, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | A_1='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_446, c_437])).
% 2.99/1.49  tff(c_533, plain, (![A_228, B_229, D_230]: (r2_hidden('#skF_7'(A_228, B_229, k2_zfmisc_1(A_228, B_229), D_230), B_229) | ~r2_hidden(D_230, k2_zfmisc_1(A_228, B_229)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.99/1.49  tff(c_439, plain, (![A_3]: (r1_xboole_0(A_3, '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_436, c_4])).
% 2.99/1.49  tff(c_447, plain, (![A_3]: (r1_xboole_0(A_3, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_446, c_439])).
% 2.99/1.49  tff(c_476, plain, (![A_197, C_198, B_199]: (~r2_hidden(A_197, C_198) | ~r1_xboole_0(k2_tarski(A_197, B_199), C_198))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.99/1.49  tff(c_481, plain, (![A_197]: (~r2_hidden(A_197, '#skF_9'))), inference(resolution, [status(thm)], [c_447, c_476])).
% 2.99/1.49  tff(c_588, plain, (![D_234, A_235]: (~r2_hidden(D_234, k2_zfmisc_1(A_235, '#skF_9')))), inference(resolution, [status(thm)], [c_533, c_481])).
% 2.99/1.49  tff(c_611, plain, (![A_235]: (k2_zfmisc_1(A_235, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_463, c_588])).
% 2.99/1.49  tff(c_449, plain, (k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_446, c_436])).
% 2.99/1.49  tff(c_50, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0 | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.99/1.49  tff(c_462, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_449, c_446, c_449, c_50])).
% 2.99/1.49  tff(c_615, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_611, c_462])).
% 2.99/1.49  tff(c_616, plain, ('#skF_11'='#skF_8'), inference(splitRight, [status(thm)], [c_445])).
% 2.99/1.49  tff(c_635, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | A_1='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_616, c_437])).
% 2.99/1.49  tff(c_700, plain, (![A_268, B_269, D_270]: (r2_hidden('#skF_6'(A_268, B_269, k2_zfmisc_1(A_268, B_269), D_270), A_268) | ~r2_hidden(D_270, k2_zfmisc_1(A_268, B_269)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.99/1.49  tff(c_618, plain, (![A_3]: (r1_xboole_0(A_3, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_616, c_439])).
% 2.99/1.49  tff(c_648, plain, (![A_240, C_241, B_242]: (~r2_hidden(A_240, C_241) | ~r1_xboole_0(k2_tarski(A_240, B_242), C_241))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.99/1.49  tff(c_653, plain, (![A_240]: (~r2_hidden(A_240, '#skF_8'))), inference(resolution, [status(thm)], [c_618, c_648])).
% 2.99/1.49  tff(c_706, plain, (![D_271, B_272]: (~r2_hidden(D_271, k2_zfmisc_1('#skF_8', B_272)))), inference(resolution, [status(thm)], [c_700, c_653])).
% 2.99/1.49  tff(c_721, plain, (![B_272]: (k2_zfmisc_1('#skF_8', B_272)='#skF_8')), inference(resolution, [status(thm)], [c_635, c_706])).
% 2.99/1.49  tff(c_620, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_616, c_436])).
% 2.99/1.49  tff(c_632, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_620, c_616, c_620, c_50])).
% 2.99/1.49  tff(c_736, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_721, c_632])).
% 2.99/1.49  tff(c_738, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_54])).
% 2.99/1.49  tff(c_56, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.99/1.49  tff(c_746, plain, ('#skF_10'='#skF_9' | '#skF_10'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_738, c_738, c_738, c_56])).
% 2.99/1.49  tff(c_747, plain, ('#skF_10'='#skF_8'), inference(splitLeft, [status(thm)], [c_746])).
% 2.99/1.49  tff(c_749, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_747, c_738])).
% 2.99/1.49  tff(c_760, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | A_1='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_749, c_2])).
% 2.99/1.49  tff(c_832, plain, (![A_312, B_313, D_314]: (r2_hidden('#skF_6'(A_312, B_313, k2_zfmisc_1(A_312, B_313), D_314), A_312) | ~r2_hidden(D_314, k2_zfmisc_1(A_312, B_313)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.99/1.49  tff(c_739, plain, (![A_3]: (r1_xboole_0(A_3, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_738, c_4])).
% 2.99/1.49  tff(c_748, plain, (![A_3]: (r1_xboole_0(A_3, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_747, c_739])).
% 2.99/1.49  tff(c_775, plain, (![A_281, C_282, B_283]: (~r2_hidden(A_281, C_282) | ~r1_xboole_0(k2_tarski(A_281, B_283), C_282))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.99/1.49  tff(c_780, plain, (![A_281]: (~r2_hidden(A_281, '#skF_8'))), inference(resolution, [status(thm)], [c_748, c_775])).
% 2.99/1.49  tff(c_887, plain, (![D_318, B_319]: (~r2_hidden(D_318, k2_zfmisc_1('#skF_8', B_319)))), inference(resolution, [status(thm)], [c_832, c_780])).
% 2.99/1.49  tff(c_910, plain, (![B_319]: (k2_zfmisc_1('#skF_8', B_319)='#skF_8')), inference(resolution, [status(thm)], [c_760, c_887])).
% 2.99/1.49  tff(c_737, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 2.99/1.49  tff(c_759, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_749, c_737])).
% 2.99/1.49  tff(c_914, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_910, c_759])).
% 2.99/1.49  tff(c_915, plain, ('#skF_10'='#skF_9'), inference(splitRight, [status(thm)], [c_746])).
% 2.99/1.49  tff(c_918, plain, (k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_915, c_738])).
% 2.99/1.49  tff(c_933, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | A_1='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_918, c_2])).
% 2.99/1.49  tff(c_1020, plain, (![A_357, B_358, D_359]: (r2_hidden('#skF_7'(A_357, B_358, k2_zfmisc_1(A_357, B_358), D_359), B_358) | ~r2_hidden(D_359, k2_zfmisc_1(A_357, B_358)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.99/1.49  tff(c_917, plain, (![A_3]: (r1_xboole_0(A_3, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_915, c_739])).
% 2.99/1.49  tff(c_946, plain, (![A_324, C_325, B_326]: (~r2_hidden(A_324, C_325) | ~r1_xboole_0(k2_tarski(A_324, B_326), C_325))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.99/1.49  tff(c_951, plain, (![A_324]: (~r2_hidden(A_324, '#skF_9'))), inference(resolution, [status(thm)], [c_917, c_946])).
% 2.99/1.49  tff(c_1059, plain, (![D_361, A_362]: (~r2_hidden(D_361, k2_zfmisc_1(A_362, '#skF_9')))), inference(resolution, [status(thm)], [c_1020, c_951])).
% 2.99/1.49  tff(c_1082, plain, (![A_362]: (k2_zfmisc_1(A_362, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_933, c_1059])).
% 2.99/1.49  tff(c_929, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_918, c_737])).
% 2.99/1.49  tff(c_1086, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1082, c_929])).
% 2.99/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.49  
% 2.99/1.49  Inference rules
% 2.99/1.49  ----------------------
% 2.99/1.49  #Ref     : 0
% 2.99/1.49  #Sup     : 198
% 2.99/1.49  #Fact    : 0
% 2.99/1.49  #Define  : 0
% 2.99/1.49  #Split   : 9
% 2.99/1.49  #Chain   : 0
% 2.99/1.49  #Close   : 0
% 2.99/1.49  
% 2.99/1.49  Ordering : KBO
% 2.99/1.49  
% 2.99/1.49  Simplification rules
% 2.99/1.49  ----------------------
% 2.99/1.49  #Subsume      : 58
% 2.99/1.49  #Demod        : 118
% 2.99/1.49  #Tautology    : 118
% 2.99/1.49  #SimpNegUnit  : 21
% 2.99/1.49  #BackRed      : 39
% 2.99/1.49  
% 2.99/1.49  #Partial instantiations: 0
% 2.99/1.49  #Strategies tried      : 1
% 2.99/1.49  
% 2.99/1.49  Timing (in seconds)
% 2.99/1.49  ----------------------
% 2.99/1.49  Preprocessing        : 0.34
% 2.99/1.49  Parsing              : 0.18
% 2.99/1.49  CNF conversion       : 0.03
% 2.99/1.49  Main loop            : 0.33
% 2.99/1.49  Inferencing          : 0.13
% 2.99/1.49  Reduction            : 0.09
% 2.99/1.49  Demodulation         : 0.06
% 2.99/1.49  BG Simplification    : 0.03
% 2.99/1.49  Subsumption          : 0.05
% 2.99/1.49  Abstraction          : 0.02
% 2.99/1.49  MUC search           : 0.00
% 2.99/1.50  Cooper               : 0.00
% 2.99/1.50  Total                : 0.72
% 2.99/1.50  Index Insertion      : 0.00
% 2.99/1.50  Index Deletion       : 0.00
% 2.99/1.50  Index Matching       : 0.00
% 2.99/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
