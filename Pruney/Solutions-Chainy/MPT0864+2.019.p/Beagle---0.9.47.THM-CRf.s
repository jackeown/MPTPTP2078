%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:11 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 181 expanded)
%              Number of leaves         :   36 (  76 expanded)
%              Depth                    :    9
%              Number of atoms          :  102 ( 287 expanded)
%              Number of equality atoms :   54 ( 199 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_11 > #skF_8 > #skF_4 > #skF_10 > #skF_9 > #skF_3 > #skF_2 > #skF_7 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

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

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_59,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_62,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_112,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_102,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_71,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_48,plain,(
    ! [B_23] : k2_zfmisc_1(k1_xboole_0,B_23) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_50,plain,(
    ! [A_24] : m1_subset_1('#skF_5'(A_24),A_24) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_222,plain,(
    ! [A_91,B_92] :
      ( r1_tarski(A_91,B_92)
      | ~ m1_subset_1(A_91,k1_zfmisc_1(B_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_227,plain,(
    ! [B_92] : r1_tarski('#skF_5'(k1_zfmisc_1(B_92)),B_92) ),
    inference(resolution,[status(thm)],[c_50,c_222])).

tff(c_74,plain,
    ( k2_mcart_1('#skF_9') = '#skF_9'
    | k1_mcart_1('#skF_9') = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_139,plain,(
    k1_mcart_1('#skF_9') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_76,plain,(
    k4_tarski('#skF_10','#skF_11') = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_127,plain,(
    ! [A_74,B_75] : k1_mcart_1(k4_tarski(A_74,B_75)) = A_74 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_136,plain,(
    k1_mcart_1('#skF_9') = '#skF_10' ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_127])).

tff(c_144,plain,(
    '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_136])).

tff(c_145,plain,(
    k4_tarski('#skF_9','#skF_11') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_76])).

tff(c_46,plain,(
    ! [A_22] : k2_zfmisc_1(A_22,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_295,plain,(
    ! [A_109,C_110,B_111,D_112] :
      ( r2_hidden(A_109,C_110)
      | ~ r2_hidden(k4_tarski(A_109,B_111),k2_zfmisc_1(C_110,D_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_305,plain,(
    ! [A_113,A_114,B_115] :
      ( r2_hidden(A_113,A_114)
      | ~ r2_hidden(k4_tarski(A_113,B_115),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_295])).

tff(c_307,plain,(
    ! [A_114] :
      ( r2_hidden('#skF_9',A_114)
      | ~ r2_hidden('#skF_9',k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_305])).

tff(c_308,plain,(
    ~ r2_hidden('#skF_9',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_307])).

tff(c_180,plain,(
    ! [A_80] :
      ( r2_hidden('#skF_8'(A_80),A_80)
      | k1_xboole_0 = A_80 ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_185,plain,(
    ! [A_1] :
      ( '#skF_8'(k1_tarski(A_1)) = A_1
      | k1_tarski(A_1) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_180,c_2])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_341,plain,(
    ! [C_129,A_130,D_131] :
      ( ~ r2_hidden(C_129,A_130)
      | k4_tarski(C_129,D_131) != '#skF_8'(A_130)
      | k1_xboole_0 = A_130 ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_358,plain,(
    ! [C_134,D_135] :
      ( k4_tarski(C_134,D_135) != '#skF_8'(k1_tarski(C_134))
      | k1_tarski(C_134) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_341])).

tff(c_383,plain,(
    ! [A_143,D_144] :
      ( k4_tarski(A_143,D_144) != A_143
      | k1_tarski(A_143) = k1_xboole_0
      | k1_tarski(A_143) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_358])).

tff(c_387,plain,(
    k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_383])).

tff(c_406,plain,(
    r2_hidden('#skF_9',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_387,c_4])).

tff(c_413,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_308,c_406])).

tff(c_416,plain,(
    ! [A_145] : r2_hidden('#skF_9',A_145) ),
    inference(splitRight,[status(thm)],[c_307])).

tff(c_56,plain,(
    ! [B_29,A_28] :
      ( ~ r1_tarski(B_29,A_28)
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_510,plain,(
    ! [A_1218] : ~ r1_tarski(A_1218,'#skF_9') ),
    inference(resolution,[status(thm)],[c_416,c_56])).

tff(c_516,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_227,c_510])).

tff(c_517,plain,(
    k2_mcart_1('#skF_9') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_528,plain,(
    ! [A_1252,B_1253] : k2_mcart_1(k4_tarski(A_1252,B_1253)) = B_1253 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_537,plain,(
    k2_mcart_1('#skF_9') = '#skF_11' ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_528])).

tff(c_540,plain,(
    '#skF_11' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_517,c_537])).

tff(c_541,plain,(
    k4_tarski('#skF_10','#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_76])).

tff(c_679,plain,(
    ! [B_1285,D_1286,A_1287,C_1288] :
      ( r2_hidden(B_1285,D_1286)
      | ~ r2_hidden(k4_tarski(A_1287,B_1285),k2_zfmisc_1(C_1288,D_1286)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_689,plain,(
    ! [D_1289,C_1290] :
      ( r2_hidden('#skF_9',D_1289)
      | ~ r2_hidden('#skF_9',k2_zfmisc_1(C_1290,D_1289)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_679])).

tff(c_695,plain,(
    ! [B_23] :
      ( r2_hidden('#skF_9',B_23)
      | ~ r2_hidden('#skF_9',k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_689])).

tff(c_696,plain,(
    ~ r2_hidden('#skF_9',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_695])).

tff(c_68,plain,(
    ! [A_53] :
      ( r2_hidden('#skF_8'(A_53),A_53)
      | k1_xboole_0 = A_53 ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_559,plain,(
    ! [C_1255,A_1256] :
      ( C_1255 = A_1256
      | ~ r2_hidden(C_1255,k1_tarski(A_1256)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_567,plain,(
    ! [A_1256] :
      ( '#skF_8'(k1_tarski(A_1256)) = A_1256
      | k1_tarski(A_1256) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_68,c_559])).

tff(c_705,plain,(
    ! [D_1296,A_1297,C_1298] :
      ( ~ r2_hidden(D_1296,A_1297)
      | k4_tarski(C_1298,D_1296) != '#skF_8'(A_1297)
      | k1_xboole_0 = A_1297 ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_742,plain,(
    ! [C_1310,C_1311] :
      ( k4_tarski(C_1310,C_1311) != '#skF_8'(k1_tarski(C_1311))
      | k1_tarski(C_1311) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_705])).

tff(c_767,plain,(
    ! [C_1319,A_1320] :
      ( k4_tarski(C_1319,A_1320) != A_1320
      | k1_tarski(A_1320) = k1_xboole_0
      | k1_tarski(A_1320) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_567,c_742])).

tff(c_771,plain,(
    k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_767])).

tff(c_791,plain,(
    r2_hidden('#skF_9',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_771,c_4])).

tff(c_798,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_696,c_791])).

tff(c_803,plain,(
    ! [B_1323] : r2_hidden('#skF_9',B_1323) ),
    inference(splitRight,[status(thm)],[c_695])).

tff(c_818,plain,(
    ! [A_1324] : A_1324 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_803,c_2])).

tff(c_518,plain,(
    k1_mcart_1('#skF_9') != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_523,plain,(
    '#skF_10' != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_518])).

tff(c_896,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_818,c_523])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:16:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.00/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.50  
% 3.00/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.50  %$ r2_hidden > r1_tarski > m1_subset_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_11 > #skF_8 > #skF_4 > #skF_10 > #skF_9 > #skF_3 > #skF_2 > #skF_7 > #skF_1
% 3.00/1.50  
% 3.00/1.50  %Foreground sorts:
% 3.00/1.50  
% 3.00/1.50  
% 3.00/1.50  %Background operators:
% 3.00/1.50  
% 3.00/1.50  
% 3.00/1.50  %Foreground operators:
% 3.00/1.50  tff('#skF_5', type, '#skF_5': $i > $i).
% 3.00/1.50  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.00/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.00/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.00/1.50  tff('#skF_11', type, '#skF_11': $i).
% 3.00/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.00/1.50  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.00/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.00/1.50  tff('#skF_8', type, '#skF_8': $i > $i).
% 3.00/1.50  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.00/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.00/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.00/1.50  tff('#skF_10', type, '#skF_10': $i).
% 3.00/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.00/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.00/1.50  tff('#skF_9', type, '#skF_9': $i).
% 3.00/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.00/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.00/1.50  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.00/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.00/1.50  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.00/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.00/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.00/1.50  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.00/1.50  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.00/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.00/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.00/1.50  
% 3.00/1.52  tff(f_59, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.00/1.52  tff(f_62, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 3.00/1.52  tff(f_66, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.00/1.52  tff(f_112, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 3.00/1.52  tff(f_86, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.00/1.52  tff(f_53, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.00/1.52  tff(f_102, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 3.00/1.52  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.00/1.52  tff(f_71, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.00/1.52  tff(c_48, plain, (![B_23]: (k2_zfmisc_1(k1_xboole_0, B_23)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.00/1.52  tff(c_50, plain, (![A_24]: (m1_subset_1('#skF_5'(A_24), A_24))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.00/1.52  tff(c_222, plain, (![A_91, B_92]: (r1_tarski(A_91, B_92) | ~m1_subset_1(A_91, k1_zfmisc_1(B_92)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.00/1.52  tff(c_227, plain, (![B_92]: (r1_tarski('#skF_5'(k1_zfmisc_1(B_92)), B_92))), inference(resolution, [status(thm)], [c_50, c_222])).
% 3.00/1.52  tff(c_74, plain, (k2_mcart_1('#skF_9')='#skF_9' | k1_mcart_1('#skF_9')='#skF_9'), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.00/1.52  tff(c_139, plain, (k1_mcart_1('#skF_9')='#skF_9'), inference(splitLeft, [status(thm)], [c_74])).
% 3.00/1.52  tff(c_76, plain, (k4_tarski('#skF_10', '#skF_11')='#skF_9'), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.00/1.52  tff(c_127, plain, (![A_74, B_75]: (k1_mcart_1(k4_tarski(A_74, B_75))=A_74)), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.00/1.52  tff(c_136, plain, (k1_mcart_1('#skF_9')='#skF_10'), inference(superposition, [status(thm), theory('equality')], [c_76, c_127])).
% 3.00/1.52  tff(c_144, plain, ('#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_139, c_136])).
% 3.00/1.52  tff(c_145, plain, (k4_tarski('#skF_9', '#skF_11')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_144, c_76])).
% 3.00/1.52  tff(c_46, plain, (![A_22]: (k2_zfmisc_1(A_22, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.00/1.52  tff(c_295, plain, (![A_109, C_110, B_111, D_112]: (r2_hidden(A_109, C_110) | ~r2_hidden(k4_tarski(A_109, B_111), k2_zfmisc_1(C_110, D_112)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.00/1.52  tff(c_305, plain, (![A_113, A_114, B_115]: (r2_hidden(A_113, A_114) | ~r2_hidden(k4_tarski(A_113, B_115), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_46, c_295])).
% 3.00/1.52  tff(c_307, plain, (![A_114]: (r2_hidden('#skF_9', A_114) | ~r2_hidden('#skF_9', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_145, c_305])).
% 3.00/1.52  tff(c_308, plain, (~r2_hidden('#skF_9', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_307])).
% 3.00/1.52  tff(c_180, plain, (![A_80]: (r2_hidden('#skF_8'(A_80), A_80) | k1_xboole_0=A_80)), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.00/1.52  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.00/1.52  tff(c_185, plain, (![A_1]: ('#skF_8'(k1_tarski(A_1))=A_1 | k1_tarski(A_1)=k1_xboole_0)), inference(resolution, [status(thm)], [c_180, c_2])).
% 3.00/1.52  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.00/1.52  tff(c_341, plain, (![C_129, A_130, D_131]: (~r2_hidden(C_129, A_130) | k4_tarski(C_129, D_131)!='#skF_8'(A_130) | k1_xboole_0=A_130)), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.00/1.52  tff(c_358, plain, (![C_134, D_135]: (k4_tarski(C_134, D_135)!='#skF_8'(k1_tarski(C_134)) | k1_tarski(C_134)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_341])).
% 3.00/1.52  tff(c_383, plain, (![A_143, D_144]: (k4_tarski(A_143, D_144)!=A_143 | k1_tarski(A_143)=k1_xboole_0 | k1_tarski(A_143)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_185, c_358])).
% 3.00/1.52  tff(c_387, plain, (k1_tarski('#skF_9')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_145, c_383])).
% 3.00/1.52  tff(c_406, plain, (r2_hidden('#skF_9', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_387, c_4])).
% 3.00/1.52  tff(c_413, plain, $false, inference(negUnitSimplification, [status(thm)], [c_308, c_406])).
% 3.00/1.52  tff(c_416, plain, (![A_145]: (r2_hidden('#skF_9', A_145))), inference(splitRight, [status(thm)], [c_307])).
% 3.00/1.52  tff(c_56, plain, (![B_29, A_28]: (~r1_tarski(B_29, A_28) | ~r2_hidden(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.00/1.52  tff(c_510, plain, (![A_1218]: (~r1_tarski(A_1218, '#skF_9'))), inference(resolution, [status(thm)], [c_416, c_56])).
% 3.00/1.52  tff(c_516, plain, $false, inference(resolution, [status(thm)], [c_227, c_510])).
% 3.00/1.52  tff(c_517, plain, (k2_mcart_1('#skF_9')='#skF_9'), inference(splitRight, [status(thm)], [c_74])).
% 3.00/1.52  tff(c_528, plain, (![A_1252, B_1253]: (k2_mcart_1(k4_tarski(A_1252, B_1253))=B_1253)), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.00/1.52  tff(c_537, plain, (k2_mcart_1('#skF_9')='#skF_11'), inference(superposition, [status(thm), theory('equality')], [c_76, c_528])).
% 3.00/1.52  tff(c_540, plain, ('#skF_11'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_517, c_537])).
% 3.00/1.52  tff(c_541, plain, (k4_tarski('#skF_10', '#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_540, c_76])).
% 3.00/1.52  tff(c_679, plain, (![B_1285, D_1286, A_1287, C_1288]: (r2_hidden(B_1285, D_1286) | ~r2_hidden(k4_tarski(A_1287, B_1285), k2_zfmisc_1(C_1288, D_1286)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.00/1.52  tff(c_689, plain, (![D_1289, C_1290]: (r2_hidden('#skF_9', D_1289) | ~r2_hidden('#skF_9', k2_zfmisc_1(C_1290, D_1289)))), inference(superposition, [status(thm), theory('equality')], [c_541, c_679])).
% 3.00/1.52  tff(c_695, plain, (![B_23]: (r2_hidden('#skF_9', B_23) | ~r2_hidden('#skF_9', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_48, c_689])).
% 3.00/1.52  tff(c_696, plain, (~r2_hidden('#skF_9', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_695])).
% 3.00/1.52  tff(c_68, plain, (![A_53]: (r2_hidden('#skF_8'(A_53), A_53) | k1_xboole_0=A_53)), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.00/1.52  tff(c_559, plain, (![C_1255, A_1256]: (C_1255=A_1256 | ~r2_hidden(C_1255, k1_tarski(A_1256)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.00/1.52  tff(c_567, plain, (![A_1256]: ('#skF_8'(k1_tarski(A_1256))=A_1256 | k1_tarski(A_1256)=k1_xboole_0)), inference(resolution, [status(thm)], [c_68, c_559])).
% 3.00/1.52  tff(c_705, plain, (![D_1296, A_1297, C_1298]: (~r2_hidden(D_1296, A_1297) | k4_tarski(C_1298, D_1296)!='#skF_8'(A_1297) | k1_xboole_0=A_1297)), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.00/1.52  tff(c_742, plain, (![C_1310, C_1311]: (k4_tarski(C_1310, C_1311)!='#skF_8'(k1_tarski(C_1311)) | k1_tarski(C_1311)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_705])).
% 3.00/1.52  tff(c_767, plain, (![C_1319, A_1320]: (k4_tarski(C_1319, A_1320)!=A_1320 | k1_tarski(A_1320)=k1_xboole_0 | k1_tarski(A_1320)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_567, c_742])).
% 3.00/1.52  tff(c_771, plain, (k1_tarski('#skF_9')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_541, c_767])).
% 3.00/1.52  tff(c_791, plain, (r2_hidden('#skF_9', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_771, c_4])).
% 3.00/1.52  tff(c_798, plain, $false, inference(negUnitSimplification, [status(thm)], [c_696, c_791])).
% 3.00/1.52  tff(c_803, plain, (![B_1323]: (r2_hidden('#skF_9', B_1323))), inference(splitRight, [status(thm)], [c_695])).
% 3.00/1.52  tff(c_818, plain, (![A_1324]: (A_1324='#skF_9')), inference(resolution, [status(thm)], [c_803, c_2])).
% 3.00/1.52  tff(c_518, plain, (k1_mcart_1('#skF_9')!='#skF_9'), inference(splitRight, [status(thm)], [c_74])).
% 3.00/1.52  tff(c_523, plain, ('#skF_10'!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_136, c_518])).
% 3.00/1.52  tff(c_896, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_818, c_523])).
% 3.00/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.52  
% 3.00/1.52  Inference rules
% 3.00/1.52  ----------------------
% 3.00/1.52  #Ref     : 0
% 3.00/1.52  #Sup     : 239
% 3.00/1.52  #Fact    : 0
% 3.00/1.52  #Define  : 0
% 3.00/1.52  #Split   : 3
% 3.00/1.52  #Chain   : 0
% 3.00/1.52  #Close   : 0
% 3.00/1.52  
% 3.00/1.52  Ordering : KBO
% 3.00/1.52  
% 3.00/1.52  Simplification rules
% 3.00/1.52  ----------------------
% 3.00/1.52  #Subsume      : 43
% 3.00/1.52  #Demod        : 29
% 3.00/1.52  #Tautology    : 77
% 3.00/1.52  #SimpNegUnit  : 4
% 3.00/1.52  #BackRed      : 3
% 3.00/1.52  
% 3.00/1.52  #Partial instantiations: 0
% 3.00/1.52  #Strategies tried      : 1
% 3.00/1.52  
% 3.00/1.52  Timing (in seconds)
% 3.00/1.52  ----------------------
% 3.00/1.52  Preprocessing        : 0.33
% 3.00/1.52  Parsing              : 0.16
% 3.00/1.52  CNF conversion       : 0.03
% 3.00/1.52  Main loop            : 0.36
% 3.00/1.52  Inferencing          : 0.15
% 3.00/1.52  Reduction            : 0.10
% 3.00/1.52  Demodulation         : 0.07
% 3.00/1.52  BG Simplification    : 0.03
% 3.00/1.52  Subsumption          : 0.05
% 3.00/1.52  Abstraction          : 0.02
% 3.00/1.52  MUC search           : 0.00
% 3.00/1.52  Cooper               : 0.00
% 3.00/1.52  Total                : 0.72
% 3.00/1.52  Index Insertion      : 0.00
% 3.00/1.52  Index Deletion       : 0.00
% 3.00/1.52  Index Matching       : 0.00
% 3.00/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
