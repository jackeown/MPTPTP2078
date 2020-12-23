%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:42 EST 2020

% Result     : Theorem 3.71s
% Output     : CNFRefutation 3.99s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 164 expanded)
%              Number of leaves         :   33 (  74 expanded)
%              Depth                    :    9
%              Number of atoms          :  164 ( 430 expanded)
%              Number of equality atoms :  129 ( 332 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_137,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & ~ ! [D] :
                ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
               => ( D != k5_mcart_1(A,B,C,D)
                  & D != k6_mcart_1(A,B,C,D)
                  & D != k7_mcart_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_mcart_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

tff(f_61,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_113,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(c_16,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_78,plain,(
    ! [A_54,B_55] : ~ r2_hidden(A_54,k2_zfmisc_1(A_54,B_55)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_81,plain,(
    ! [A_6] : ~ r2_hidden(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_78])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_48,plain,(
    m1_subset_1('#skF_8',k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1801,plain,(
    ! [A_398,B_399,C_400,D_401] :
      ( k7_mcart_1(A_398,B_399,C_400,D_401) = k2_mcart_1(D_401)
      | ~ m1_subset_1(D_401,k3_zfmisc_1(A_398,B_399,C_400))
      | k1_xboole_0 = C_400
      | k1_xboole_0 = B_399
      | k1_xboole_0 = A_398 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1816,plain,
    ( k7_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_48,c_1801])).

tff(c_1822,plain,(
    k7_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_52,c_50,c_1816])).

tff(c_605,plain,(
    ! [A_167,B_168,C_169,D_170] :
      ( k7_mcart_1(A_167,B_168,C_169,D_170) = k2_mcart_1(D_170)
      | ~ m1_subset_1(D_170,k3_zfmisc_1(A_167,B_168,C_169))
      | k1_xboole_0 = C_169
      | k1_xboole_0 = B_168
      | k1_xboole_0 = A_167 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_620,plain,
    ( k7_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_48,c_605])).

tff(c_626,plain,(
    k7_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_52,c_50,c_620])).

tff(c_46,plain,
    ( k7_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = '#skF_8'
    | k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = '#skF_8'
    | k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_214,plain,(
    k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_761,plain,(
    ! [A_195,B_196,C_197,D_198] :
      ( k3_mcart_1(k5_mcart_1(A_195,B_196,C_197,D_198),k6_mcart_1(A_195,B_196,C_197,D_198),k7_mcart_1(A_195,B_196,C_197,D_198)) = D_198
      | ~ m1_subset_1(D_198,k3_zfmisc_1(A_195,B_196,C_197))
      | k1_xboole_0 = C_197
      | k1_xboole_0 = B_196
      | k1_xboole_0 = A_195 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_794,plain,
    ( k3_mcart_1('#skF_8',k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8'),k7_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8')) = '#skF_8'
    | ~ m1_subset_1('#skF_8',k3_zfmisc_1('#skF_5','#skF_6','#skF_7'))
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_761])).

tff(c_801,plain,
    ( k3_mcart_1('#skF_8',k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8'),k2_mcart_1('#skF_8')) = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_626,c_794])).

tff(c_802,plain,(
    k3_mcart_1('#skF_8',k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8'),k2_mcart_1('#skF_8')) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_52,c_50,c_801])).

tff(c_26,plain,(
    ! [A_16] :
      ( r2_hidden('#skF_3'(A_16),A_16)
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_100,plain,(
    ! [C_59,A_60] :
      ( C_59 = A_60
      | ~ r2_hidden(C_59,k1_tarski(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_113,plain,(
    ! [A_60] :
      ( '#skF_3'(k1_tarski(A_60)) = A_60
      | k1_tarski(A_60) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_100])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_382,plain,(
    ! [C_126,A_127,D_128,E_129] :
      ( ~ r2_hidden(C_126,A_127)
      | k3_mcart_1(C_126,D_128,E_129) != '#skF_3'(A_127)
      | k1_xboole_0 = A_127 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_401,plain,(
    ! [C_138,D_139,E_140] :
      ( k3_mcart_1(C_138,D_139,E_140) != '#skF_3'(k1_tarski(C_138))
      | k1_tarski(C_138) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_382])).

tff(c_404,plain,(
    ! [A_60,D_139,E_140] :
      ( k3_mcart_1(A_60,D_139,E_140) != A_60
      | k1_tarski(A_60) = k1_xboole_0
      | k1_tarski(A_60) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_401])).

tff(c_827,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_802,c_404])).

tff(c_856,plain,(
    r2_hidden('#skF_8',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_827,c_4])).

tff(c_867,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_856])).

tff(c_868,plain,
    ( k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = '#skF_8'
    | k7_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_976,plain,(
    k7_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_868])).

tff(c_1416,plain,(
    ! [A_321,B_322,C_323,D_324] :
      ( k3_mcart_1(k5_mcart_1(A_321,B_322,C_323,D_324),k6_mcart_1(A_321,B_322,C_323,D_324),k7_mcart_1(A_321,B_322,C_323,D_324)) = D_324
      | ~ m1_subset_1(D_324,k3_zfmisc_1(A_321,B_322,C_323))
      | k1_xboole_0 = C_323
      | k1_xboole_0 = B_322
      | k1_xboole_0 = A_321 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1446,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8'),k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_8') = '#skF_8'
    | ~ m1_subset_1('#skF_8',k3_zfmisc_1('#skF_5','#skF_6','#skF_7'))
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_976,c_1416])).

tff(c_1450,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8'),k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_8') = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1446])).

tff(c_1451,plain,(
    k3_mcart_1(k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8'),k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_8') = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_52,c_50,c_1450])).

tff(c_40,plain,(
    ! [A_40] :
      ( r2_hidden('#skF_4'(A_40),A_40)
      | k1_xboole_0 = A_40 ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_112,plain,(
    ! [A_60] :
      ( '#skF_4'(k1_tarski(A_60)) = A_60
      | k1_tarski(A_60) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_100])).

tff(c_22,plain,(
    ! [A_10,B_11,C_12] : k4_tarski(k4_tarski(A_10,B_11),C_12) = k3_mcart_1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_946,plain,(
    ! [D_211,A_212,C_213] :
      ( ~ r2_hidden(D_211,A_212)
      | k4_tarski(C_213,D_211) != '#skF_4'(A_212)
      | k1_xboole_0 = A_212 ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_981,plain,(
    ! [C_220,C_221] :
      ( k4_tarski(C_220,C_221) != '#skF_4'(k1_tarski(C_221))
      | k1_tarski(C_221) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_946])).

tff(c_1056,plain,(
    ! [A_262,B_263,C_264] :
      ( k3_mcart_1(A_262,B_263,C_264) != '#skF_4'(k1_tarski(C_264))
      | k1_tarski(C_264) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_981])).

tff(c_1059,plain,(
    ! [A_262,B_263,A_60] :
      ( k3_mcart_1(A_262,B_263,A_60) != A_60
      | k1_tarski(A_60) = k1_xboole_0
      | k1_tarski(A_60) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_1056])).

tff(c_1476,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1451,c_1059])).

tff(c_1505,plain,(
    r2_hidden('#skF_8',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1476,c_4])).

tff(c_1516,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_1505])).

tff(c_1517,plain,(
    k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_868])).

tff(c_1957,plain,(
    ! [A_426,B_427,C_428,D_429] :
      ( k3_mcart_1(k5_mcart_1(A_426,B_427,C_428,D_429),k6_mcart_1(A_426,B_427,C_428,D_429),k7_mcart_1(A_426,B_427,C_428,D_429)) = D_429
      | ~ m1_subset_1(D_429,k3_zfmisc_1(A_426,B_427,C_428))
      | k1_xboole_0 = C_428
      | k1_xboole_0 = B_427
      | k1_xboole_0 = A_426 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1990,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_8',k7_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8')) = '#skF_8'
    | ~ m1_subset_1('#skF_8',k3_zfmisc_1('#skF_5','#skF_6','#skF_7'))
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1517,c_1957])).

tff(c_1997,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_8',k2_mcart_1('#skF_8')) = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1822,c_1990])).

tff(c_1998,plain,(
    k3_mcart_1(k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8'),'#skF_8',k2_mcart_1('#skF_8')) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_52,c_50,c_1997])).

tff(c_1549,plain,(
    ! [D_337,A_338,C_339,E_340] :
      ( ~ r2_hidden(D_337,A_338)
      | k3_mcart_1(C_339,D_337,E_340) != '#skF_3'(A_338)
      | k1_xboole_0 = A_338 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1567,plain,(
    ! [C_347,C_348,E_349] :
      ( k3_mcart_1(C_347,C_348,E_349) != '#skF_3'(k1_tarski(C_348))
      | k1_tarski(C_348) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_1549])).

tff(c_1570,plain,(
    ! [C_347,A_60,E_349] :
      ( k3_mcart_1(C_347,A_60,E_349) != A_60
      | k1_tarski(A_60) = k1_xboole_0
      | k1_tarski(A_60) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_1567])).

tff(c_2023,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1998,c_1570])).

tff(c_2052,plain,(
    r2_hidden('#skF_8',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2023,c_4])).

tff(c_2063,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_2052])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:55:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.71/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.71/1.68  
% 3.71/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.71/1.69  %$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_1
% 3.71/1.69  
% 3.71/1.69  %Foreground sorts:
% 3.71/1.69  
% 3.71/1.69  
% 3.71/1.69  %Background operators:
% 3.71/1.69  
% 3.71/1.69  
% 3.71/1.69  %Foreground operators:
% 3.71/1.69  tff('#skF_4', type, '#skF_4': $i > $i).
% 3.71/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.71/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.71/1.69  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.71/1.69  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.71/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.71/1.69  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.71/1.69  tff('#skF_7', type, '#skF_7': $i).
% 3.71/1.69  tff('#skF_5', type, '#skF_5': $i).
% 3.71/1.69  tff('#skF_6', type, '#skF_6': $i).
% 3.71/1.69  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 3.71/1.69  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.71/1.69  tff('#skF_8', type, '#skF_8': $i).
% 3.71/1.69  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 3.71/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.71/1.69  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.71/1.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.71/1.69  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.71/1.69  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 3.71/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.71/1.69  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.71/1.69  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.71/1.69  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.71/1.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.71/1.69  
% 3.99/1.70  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.99/1.70  tff(f_41, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.99/1.70  tff(f_137, negated_conjecture, ~(![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => ((~(D = k5_mcart_1(A, B, C, D)) & ~(D = k6_mcart_1(A, B, C, D))) & ~(D = k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_mcart_1)).
% 3.99/1.70  tff(f_97, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 3.99/1.70  tff(f_77, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_mcart_1)).
% 3.99/1.70  tff(f_61, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 3.99/1.70  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.99/1.70  tff(f_113, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 3.99/1.70  tff(f_43, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 3.99/1.70  tff(c_16, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.99/1.70  tff(c_78, plain, (![A_54, B_55]: (~r2_hidden(A_54, k2_zfmisc_1(A_54, B_55)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.99/1.70  tff(c_81, plain, (![A_6]: (~r2_hidden(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_78])).
% 3.99/1.70  tff(c_54, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.99/1.70  tff(c_52, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.99/1.70  tff(c_50, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.99/1.70  tff(c_48, plain, (m1_subset_1('#skF_8', k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.99/1.70  tff(c_1801, plain, (![A_398, B_399, C_400, D_401]: (k7_mcart_1(A_398, B_399, C_400, D_401)=k2_mcart_1(D_401) | ~m1_subset_1(D_401, k3_zfmisc_1(A_398, B_399, C_400)) | k1_xboole_0=C_400 | k1_xboole_0=B_399 | k1_xboole_0=A_398)), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.99/1.70  tff(c_1816, plain, (k7_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_48, c_1801])).
% 3.99/1.70  tff(c_1822, plain, (k7_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k2_mcart_1('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_54, c_52, c_50, c_1816])).
% 3.99/1.70  tff(c_605, plain, (![A_167, B_168, C_169, D_170]: (k7_mcart_1(A_167, B_168, C_169, D_170)=k2_mcart_1(D_170) | ~m1_subset_1(D_170, k3_zfmisc_1(A_167, B_168, C_169)) | k1_xboole_0=C_169 | k1_xboole_0=B_168 | k1_xboole_0=A_167)), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.99/1.70  tff(c_620, plain, (k7_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_48, c_605])).
% 3.99/1.70  tff(c_626, plain, (k7_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k2_mcart_1('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_54, c_52, c_50, c_620])).
% 3.99/1.70  tff(c_46, plain, (k7_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')='#skF_8' | k6_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')='#skF_8' | k5_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')='#skF_8'), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.99/1.70  tff(c_214, plain, (k5_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')='#skF_8'), inference(splitLeft, [status(thm)], [c_46])).
% 3.99/1.70  tff(c_761, plain, (![A_195, B_196, C_197, D_198]: (k3_mcart_1(k5_mcart_1(A_195, B_196, C_197, D_198), k6_mcart_1(A_195, B_196, C_197, D_198), k7_mcart_1(A_195, B_196, C_197, D_198))=D_198 | ~m1_subset_1(D_198, k3_zfmisc_1(A_195, B_196, C_197)) | k1_xboole_0=C_197 | k1_xboole_0=B_196 | k1_xboole_0=A_195)), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.99/1.70  tff(c_794, plain, (k3_mcart_1('#skF_8', k6_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'), k7_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))='#skF_8' | ~m1_subset_1('#skF_8', k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')) | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_214, c_761])).
% 3.99/1.70  tff(c_801, plain, (k3_mcart_1('#skF_8', k6_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'), k2_mcart_1('#skF_8'))='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_626, c_794])).
% 3.99/1.70  tff(c_802, plain, (k3_mcart_1('#skF_8', k6_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'), k2_mcart_1('#skF_8'))='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_54, c_52, c_50, c_801])).
% 3.99/1.70  tff(c_26, plain, (![A_16]: (r2_hidden('#skF_3'(A_16), A_16) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.99/1.70  tff(c_100, plain, (![C_59, A_60]: (C_59=A_60 | ~r2_hidden(C_59, k1_tarski(A_60)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.99/1.70  tff(c_113, plain, (![A_60]: ('#skF_3'(k1_tarski(A_60))=A_60 | k1_tarski(A_60)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_100])).
% 3.99/1.70  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.99/1.70  tff(c_382, plain, (![C_126, A_127, D_128, E_129]: (~r2_hidden(C_126, A_127) | k3_mcart_1(C_126, D_128, E_129)!='#skF_3'(A_127) | k1_xboole_0=A_127)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.99/1.70  tff(c_401, plain, (![C_138, D_139, E_140]: (k3_mcart_1(C_138, D_139, E_140)!='#skF_3'(k1_tarski(C_138)) | k1_tarski(C_138)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_382])).
% 3.99/1.70  tff(c_404, plain, (![A_60, D_139, E_140]: (k3_mcart_1(A_60, D_139, E_140)!=A_60 | k1_tarski(A_60)=k1_xboole_0 | k1_tarski(A_60)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_113, c_401])).
% 3.99/1.70  tff(c_827, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_802, c_404])).
% 3.99/1.70  tff(c_856, plain, (r2_hidden('#skF_8', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_827, c_4])).
% 3.99/1.70  tff(c_867, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_856])).
% 3.99/1.70  tff(c_868, plain, (k6_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')='#skF_8' | k7_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')='#skF_8'), inference(splitRight, [status(thm)], [c_46])).
% 3.99/1.70  tff(c_976, plain, (k7_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')='#skF_8'), inference(splitLeft, [status(thm)], [c_868])).
% 3.99/1.70  tff(c_1416, plain, (![A_321, B_322, C_323, D_324]: (k3_mcart_1(k5_mcart_1(A_321, B_322, C_323, D_324), k6_mcart_1(A_321, B_322, C_323, D_324), k7_mcart_1(A_321, B_322, C_323, D_324))=D_324 | ~m1_subset_1(D_324, k3_zfmisc_1(A_321, B_322, C_323)) | k1_xboole_0=C_323 | k1_xboole_0=B_322 | k1_xboole_0=A_321)), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.99/1.70  tff(c_1446, plain, (k3_mcart_1(k5_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'), k6_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_8')='#skF_8' | ~m1_subset_1('#skF_8', k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')) | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_976, c_1416])).
% 3.99/1.70  tff(c_1450, plain, (k3_mcart_1(k5_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'), k6_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_8')='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1446])).
% 3.99/1.70  tff(c_1451, plain, (k3_mcart_1(k5_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'), k6_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_8')='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_54, c_52, c_50, c_1450])).
% 3.99/1.70  tff(c_40, plain, (![A_40]: (r2_hidden('#skF_4'(A_40), A_40) | k1_xboole_0=A_40)), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.99/1.70  tff(c_112, plain, (![A_60]: ('#skF_4'(k1_tarski(A_60))=A_60 | k1_tarski(A_60)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_100])).
% 3.99/1.70  tff(c_22, plain, (![A_10, B_11, C_12]: (k4_tarski(k4_tarski(A_10, B_11), C_12)=k3_mcart_1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.99/1.70  tff(c_946, plain, (![D_211, A_212, C_213]: (~r2_hidden(D_211, A_212) | k4_tarski(C_213, D_211)!='#skF_4'(A_212) | k1_xboole_0=A_212)), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.99/1.70  tff(c_981, plain, (![C_220, C_221]: (k4_tarski(C_220, C_221)!='#skF_4'(k1_tarski(C_221)) | k1_tarski(C_221)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_946])).
% 3.99/1.70  tff(c_1056, plain, (![A_262, B_263, C_264]: (k3_mcart_1(A_262, B_263, C_264)!='#skF_4'(k1_tarski(C_264)) | k1_tarski(C_264)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_981])).
% 3.99/1.70  tff(c_1059, plain, (![A_262, B_263, A_60]: (k3_mcart_1(A_262, B_263, A_60)!=A_60 | k1_tarski(A_60)=k1_xboole_0 | k1_tarski(A_60)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_112, c_1056])).
% 3.99/1.70  tff(c_1476, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1451, c_1059])).
% 3.99/1.70  tff(c_1505, plain, (r2_hidden('#skF_8', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1476, c_4])).
% 3.99/1.70  tff(c_1516, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_1505])).
% 3.99/1.70  tff(c_1517, plain, (k6_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')='#skF_8'), inference(splitRight, [status(thm)], [c_868])).
% 3.99/1.70  tff(c_1957, plain, (![A_426, B_427, C_428, D_429]: (k3_mcart_1(k5_mcart_1(A_426, B_427, C_428, D_429), k6_mcart_1(A_426, B_427, C_428, D_429), k7_mcart_1(A_426, B_427, C_428, D_429))=D_429 | ~m1_subset_1(D_429, k3_zfmisc_1(A_426, B_427, C_428)) | k1_xboole_0=C_428 | k1_xboole_0=B_427 | k1_xboole_0=A_426)), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.99/1.70  tff(c_1990, plain, (k3_mcart_1(k5_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_8', k7_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))='#skF_8' | ~m1_subset_1('#skF_8', k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')) | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1517, c_1957])).
% 3.99/1.70  tff(c_1997, plain, (k3_mcart_1(k5_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_8', k2_mcart_1('#skF_8'))='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1822, c_1990])).
% 3.99/1.70  tff(c_1998, plain, (k3_mcart_1(k5_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'), '#skF_8', k2_mcart_1('#skF_8'))='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_54, c_52, c_50, c_1997])).
% 3.99/1.70  tff(c_1549, plain, (![D_337, A_338, C_339, E_340]: (~r2_hidden(D_337, A_338) | k3_mcart_1(C_339, D_337, E_340)!='#skF_3'(A_338) | k1_xboole_0=A_338)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.99/1.70  tff(c_1567, plain, (![C_347, C_348, E_349]: (k3_mcart_1(C_347, C_348, E_349)!='#skF_3'(k1_tarski(C_348)) | k1_tarski(C_348)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_1549])).
% 3.99/1.70  tff(c_1570, plain, (![C_347, A_60, E_349]: (k3_mcart_1(C_347, A_60, E_349)!=A_60 | k1_tarski(A_60)=k1_xboole_0 | k1_tarski(A_60)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_113, c_1567])).
% 3.99/1.70  tff(c_2023, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1998, c_1570])).
% 3.99/1.70  tff(c_2052, plain, (r2_hidden('#skF_8', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2023, c_4])).
% 3.99/1.70  tff(c_2063, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_2052])).
% 3.99/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.99/1.70  
% 3.99/1.70  Inference rules
% 3.99/1.70  ----------------------
% 3.99/1.70  #Ref     : 0
% 3.99/1.70  #Sup     : 514
% 3.99/1.70  #Fact    : 0
% 3.99/1.70  #Define  : 0
% 3.99/1.70  #Split   : 2
% 3.99/1.70  #Chain   : 0
% 3.99/1.70  #Close   : 0
% 3.99/1.70  
% 3.99/1.70  Ordering : KBO
% 3.99/1.70  
% 3.99/1.70  Simplification rules
% 3.99/1.70  ----------------------
% 3.99/1.70  #Subsume      : 112
% 3.99/1.70  #Demod        : 161
% 3.99/1.70  #Tautology    : 198
% 3.99/1.70  #SimpNegUnit  : 20
% 3.99/1.70  #BackRed      : 4
% 3.99/1.70  
% 3.99/1.70  #Partial instantiations: 0
% 3.99/1.70  #Strategies tried      : 1
% 3.99/1.70  
% 3.99/1.70  Timing (in seconds)
% 3.99/1.70  ----------------------
% 3.99/1.71  Preprocessing        : 0.32
% 3.99/1.71  Parsing              : 0.16
% 3.99/1.71  CNF conversion       : 0.03
% 3.99/1.71  Main loop            : 0.55
% 3.99/1.71  Inferencing          : 0.22
% 3.99/1.71  Reduction            : 0.15
% 3.99/1.71  Demodulation         : 0.10
% 3.99/1.71  BG Simplification    : 0.03
% 3.99/1.71  Subsumption          : 0.10
% 3.99/1.71  Abstraction          : 0.03
% 3.99/1.71  MUC search           : 0.00
% 3.99/1.71  Cooper               : 0.00
% 3.99/1.71  Total                : 0.90
% 3.99/1.71  Index Insertion      : 0.00
% 3.99/1.71  Index Deletion       : 0.00
% 3.99/1.71  Index Matching       : 0.00
% 3.99/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
