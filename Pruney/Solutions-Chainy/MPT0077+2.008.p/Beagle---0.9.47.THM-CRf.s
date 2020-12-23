%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:36 EST 2020

% Result     : Theorem 53.65s
% Output     : CNFRefutation 53.88s
% Verified   : 
% Statistics : Number of formulae       :  243 ( 601 expanded)
%              Number of leaves         :   26 ( 206 expanded)
%              Depth                    :   12
%              Number of atoms          :  414 (1520 expanded)
%              Number of equality atoms :  112 ( 337 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
            & r1_xboole_0(A,B)
            & r1_xboole_0(A,C) )
        & ~ ( ~ ( r1_xboole_0(A,B)
                & r1_xboole_0(A,C) )
            & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_97,plain,(
    ! [A_29,B_30] :
      ( r1_xboole_0(A_29,B_30)
      | k3_xboole_0(A_29,B_30) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26,plain,(
    ! [B_12,A_11] :
      ( r1_xboole_0(B_12,A_11)
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_154,plain,(
    ! [B_36,A_37] :
      ( r1_xboole_0(B_36,A_37)
      | k3_xboole_0(A_37,B_36) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_97,c_26])).

tff(c_42,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_6')
    | ~ r1_xboole_0('#skF_4','#skF_5')
    | r1_xboole_0('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_149,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_163,plain,(
    k3_xboole_0('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_154,c_149])).

tff(c_20,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),A_3)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_89301,plain,(
    ! [A_1731,B_1732,C_1733] :
      ( ~ r2_hidden('#skF_1'(A_1731,B_1732,C_1733),C_1733)
      | r2_hidden('#skF_2'(A_1731,B_1732,C_1733),C_1733)
      | k4_xboole_0(A_1731,B_1732) = C_1733 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_89315,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_2'(A_3,B_4,A_3),A_3)
      | k4_xboole_0(A_3,B_4) = A_3 ) ),
    inference(resolution,[status(thm)],[c_20,c_89301])).

tff(c_14,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),A_3)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),B_4)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),A_3)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_89930,plain,(
    ! [A_1752,B_1753,C_1754] :
      ( ~ r2_hidden('#skF_1'(A_1752,B_1753,C_1754),C_1754)
      | r2_hidden('#skF_2'(A_1752,B_1753,C_1754),B_1753)
      | ~ r2_hidden('#skF_2'(A_1752,B_1753,C_1754),A_1752)
      | k4_xboole_0(A_1752,B_1753) = C_1754 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_99905,plain,(
    ! [A_1958,B_1959] :
      ( r2_hidden('#skF_2'(A_1958,B_1959,A_1958),B_1959)
      | ~ r2_hidden('#skF_2'(A_1958,B_1959,A_1958),A_1958)
      | k4_xboole_0(A_1958,B_1959) = A_1958 ) ),
    inference(resolution,[status(thm)],[c_14,c_89930])).

tff(c_110891,plain,(
    ! [A_2136,B_2137] :
      ( r2_hidden('#skF_2'(A_2136,B_2137,A_2136),B_2137)
      | k4_xboole_0(A_2136,B_2137) = A_2136 ) ),
    inference(resolution,[status(thm)],[c_89315,c_99905])).

tff(c_66077,plain,(
    ! [A_1241,B_1242,C_1243] :
      ( r2_hidden('#skF_1'(A_1241,B_1242,C_1243),A_1241)
      | r2_hidden('#skF_2'(A_1241,B_1242,C_1243),C_1243)
      | k4_xboole_0(A_1241,B_1242) = C_1243 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_66128,plain,(
    ! [A_1241,B_1242] :
      ( r2_hidden('#skF_2'(A_1241,B_1242,A_1241),A_1241)
      | k4_xboole_0(A_1241,B_1242) = A_1241 ) ),
    inference(resolution,[status(thm)],[c_66077,c_16])).

tff(c_67279,plain,(
    ! [A_1282,B_1283,C_1284] :
      ( ~ r2_hidden('#skF_1'(A_1282,B_1283,C_1284),C_1284)
      | r2_hidden('#skF_2'(A_1282,B_1283,C_1284),B_1283)
      | ~ r2_hidden('#skF_2'(A_1282,B_1283,C_1284),A_1282)
      | k4_xboole_0(A_1282,B_1283) = C_1284 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_78409,plain,(
    ! [A_1465,B_1466] :
      ( r2_hidden('#skF_2'(A_1465,B_1466,A_1465),B_1466)
      | ~ r2_hidden('#skF_2'(A_1465,B_1466,A_1465),A_1465)
      | k4_xboole_0(A_1465,B_1466) = A_1465 ) ),
    inference(resolution,[status(thm)],[c_14,c_67279])).

tff(c_86760,plain,(
    ! [A_1662,B_1663] :
      ( r2_hidden('#skF_2'(A_1662,B_1663,A_1662),B_1663)
      | k4_xboole_0(A_1662,B_1663) = A_1662 ) ),
    inference(resolution,[status(thm)],[c_66128,c_78409])).

tff(c_38133,plain,(
    ! [A_710,B_711,C_712] :
      ( ~ r2_hidden('#skF_1'(A_710,B_711,C_712),C_712)
      | r2_hidden('#skF_2'(A_710,B_711,C_712),C_712)
      | k4_xboole_0(A_710,B_711) = C_712 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_38142,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_2'(A_3,B_4,A_3),A_3)
      | k4_xboole_0(A_3,B_4) = A_3 ) ),
    inference(resolution,[status(thm)],[c_20,c_38133])).

tff(c_38721,plain,(
    ! [A_732,B_733,C_734] :
      ( ~ r2_hidden('#skF_1'(A_732,B_733,C_734),C_734)
      | r2_hidden('#skF_2'(A_732,B_733,C_734),B_733)
      | ~ r2_hidden('#skF_2'(A_732,B_733,C_734),A_732)
      | k4_xboole_0(A_732,B_733) = C_734 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_47495,plain,(
    ! [A_897,B_898] :
      ( r2_hidden('#skF_2'(A_897,B_898,A_897),B_898)
      | ~ r2_hidden('#skF_2'(A_897,B_898,A_897),A_897)
      | k4_xboole_0(A_897,B_898) = A_897 ) ),
    inference(resolution,[status(thm)],[c_14,c_38721])).

tff(c_62781,plain,(
    ! [A_1175,B_1176] :
      ( r2_hidden('#skF_2'(A_1175,B_1176,A_1175),B_1176)
      | k4_xboole_0(A_1175,B_1176) = A_1175 ) ),
    inference(resolution,[status(thm)],[c_38142,c_47495])).

tff(c_100,plain,(
    ! [B_30,A_29] :
      ( r1_xboole_0(B_30,A_29)
      | k3_xboole_0(A_29,B_30) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_97,c_26])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_48,plain,
    ( r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6'))
    | ~ r1_xboole_0('#skF_7',k2_xboole_0('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_53,plain,
    ( r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5'))
    | ~ r1_xboole_0('#skF_7',k2_xboole_0('#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_48])).

tff(c_354,plain,(
    ~ r1_xboole_0('#skF_7',k2_xboole_0('#skF_8','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_53])).

tff(c_361,plain,(
    k3_xboole_0(k2_xboole_0('#skF_8','#skF_9'),'#skF_7') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_100,c_354])).

tff(c_1020,plain,(
    ! [A_95,B_96,C_97] :
      ( r2_hidden('#skF_1'(A_95,B_96,C_97),A_95)
      | r2_hidden('#skF_2'(A_95,B_96,C_97),C_97)
      | k4_xboole_0(A_95,B_96) = C_97 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1070,plain,(
    ! [A_95,B_96] :
      ( r2_hidden('#skF_2'(A_95,B_96,A_95),A_95)
      | k4_xboole_0(A_95,B_96) = A_95 ) ),
    inference(resolution,[status(thm)],[c_1020,c_16])).

tff(c_1381,plain,(
    ! [A_115,B_116,C_117] :
      ( r2_hidden('#skF_1'(A_115,B_116,C_117),A_115)
      | r2_hidden('#skF_2'(A_115,B_116,C_117),B_116)
      | ~ r2_hidden('#skF_2'(A_115,B_116,C_117),A_115)
      | k4_xboole_0(A_115,B_116) = C_117 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),B_4)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),A_3)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_11596,plain,(
    ! [A_300,B_301] :
      ( r2_hidden('#skF_2'(A_300,B_301,A_300),B_301)
      | ~ r2_hidden('#skF_2'(A_300,B_301,A_300),A_300)
      | k4_xboole_0(A_300,B_301) = A_300 ) ),
    inference(resolution,[status(thm)],[c_1381,c_10])).

tff(c_23157,plain,(
    ! [A_515,B_516] :
      ( r2_hidden('#skF_2'(A_515,B_516,A_515),B_516)
      | k4_xboole_0(A_515,B_516) = A_515 ) ),
    inference(resolution,[status(thm)],[c_1070,c_11596])).

tff(c_3795,plain,(
    ! [A_169,B_170] :
      ( r2_hidden('#skF_2'(A_169,B_170,A_169),A_169)
      | k4_xboole_0(A_169,B_170) = A_169 ) ),
    inference(resolution,[status(thm)],[c_1020,c_16])).

tff(c_44,plain,
    ( r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6'))
    | r1_xboole_0('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_51,plain,
    ( r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5'))
    | r1_xboole_0('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_44])).

tff(c_211,plain,(
    r1_xboole_0('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_51])).

tff(c_313,plain,(
    ! [A_55,B_56,C_57] :
      ( ~ r1_xboole_0(A_55,B_56)
      | ~ r2_hidden(C_57,B_56)
      | ~ r2_hidden(C_57,A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_327,plain,(
    ! [C_57] :
      ( ~ r2_hidden(C_57,'#skF_8')
      | ~ r2_hidden(C_57,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_211,c_313])).

tff(c_3844,plain,(
    ! [B_170] :
      ( ~ r2_hidden('#skF_2'('#skF_7',B_170,'#skF_7'),'#skF_8')
      | k4_xboole_0('#skF_7',B_170) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_3795,c_327])).

tff(c_23244,plain,(
    k4_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_23157,c_3844])).

tff(c_40,plain,
    ( r1_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6'))
    | r1_xboole_0('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_52,plain,
    ( r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5'))
    | r1_xboole_0('#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_40])).

tff(c_187,plain,(
    r1_xboole_0('#skF_7','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_329,plain,(
    ! [C_57] :
      ( ~ r2_hidden(C_57,'#skF_9')
      | ~ r2_hidden(C_57,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_187,c_313])).

tff(c_3843,plain,(
    ! [B_170] :
      ( ~ r2_hidden('#skF_2'('#skF_7',B_170,'#skF_7'),'#skF_9')
      | k4_xboole_0('#skF_7',B_170) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_3795,c_329])).

tff(c_23242,plain,(
    k4_xboole_0('#skF_7','#skF_9') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_23157,c_3843])).

tff(c_36,plain,(
    ! [A_19,B_20,C_21] : k4_xboole_0(k4_xboole_0(A_19,B_20),C_21) = k4_xboole_0(A_19,k2_xboole_0(B_20,C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_36584,plain,(
    ! [C_666] : k4_xboole_0('#skF_7',k2_xboole_0('#skF_9',C_666)) = k4_xboole_0('#skF_7',C_666) ),
    inference(superposition,[status(thm),theory(equality)],[c_23242,c_36])).

tff(c_30,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_3'(A_13,B_14),B_14)
      | r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_219,plain,(
    ! [A_46,B_47] :
      ( r2_hidden('#skF_3'(A_46,B_47),A_46)
      | r1_xboole_0(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5318,plain,(
    ! [A_200,B_201,B_202] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_200,B_201),B_202),B_201)
      | r1_xboole_0(k4_xboole_0(A_200,B_201),B_202) ) ),
    inference(resolution,[status(thm)],[c_219,c_6])).

tff(c_5412,plain,(
    ! [A_203,B_204] : r1_xboole_0(k4_xboole_0(A_203,B_204),B_204) ),
    inference(resolution,[status(thm)],[c_30,c_5318])).

tff(c_5482,plain,(
    ! [B_204,A_203] : r1_xboole_0(B_204,k4_xboole_0(A_203,B_204)) ),
    inference(resolution,[status(thm)],[c_5412,c_26])).

tff(c_37092,plain,(
    ! [C_667] : r1_xboole_0(k2_xboole_0('#skF_9',C_667),k4_xboole_0('#skF_7',C_667)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36584,c_5482])).

tff(c_37117,plain,(
    r1_xboole_0(k2_xboole_0('#skF_9','#skF_8'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_23244,c_37092])).

tff(c_37184,plain,(
    r1_xboole_0(k2_xboole_0('#skF_8','#skF_9'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_37117])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = k1_xboole_0
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_37204,plain,(
    k3_xboole_0(k2_xboole_0('#skF_8','#skF_9'),'#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_37184,c_22])).

tff(c_37211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_361,c_37204])).

tff(c_37212,plain,(
    r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_28,plain,(
    ! [A_13,B_14,C_17] :
      ( ~ r1_xboole_0(A_13,B_14)
      | ~ r2_hidden(C_17,B_14)
      | ~ r2_hidden(C_17,A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_37221,plain,(
    ! [C_17] :
      ( ~ r2_hidden(C_17,k2_xboole_0('#skF_6','#skF_5'))
      | ~ r2_hidden(C_17,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_37212,c_28])).

tff(c_64767,plain,(
    ! [A_1187] :
      ( ~ r2_hidden('#skF_2'(A_1187,k2_xboole_0('#skF_6','#skF_5'),A_1187),'#skF_4')
      | k4_xboole_0(A_1187,k2_xboole_0('#skF_6','#skF_5')) = A_1187 ) ),
    inference(resolution,[status(thm)],[c_62781,c_37221])).

tff(c_64776,plain,(
    k4_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38142,c_64767])).

tff(c_32,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_3'(A_13,B_14),A_13)
      | r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_250,plain,(
    ! [A_48,B_49] :
      ( r2_hidden('#skF_3'(A_48,B_49),B_49)
      | r1_xboole_0(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_42644,plain,(
    ! [A_816,A_817,B_818] :
      ( ~ r2_hidden('#skF_3'(A_816,k4_xboole_0(A_817,B_818)),B_818)
      | r1_xboole_0(A_816,k4_xboole_0(A_817,B_818)) ) ),
    inference(resolution,[status(thm)],[c_250,c_6])).

tff(c_42737,plain,(
    ! [A_819,A_820] : r1_xboole_0(A_819,k4_xboole_0(A_820,A_819)) ),
    inference(resolution,[status(thm)],[c_32,c_42644])).

tff(c_42811,plain,(
    ! [A_821,A_822] : r1_xboole_0(k4_xboole_0(A_821,A_822),A_822) ),
    inference(resolution,[status(thm)],[c_42737,c_26])).

tff(c_42869,plain,(
    ! [A_19,B_20,C_21] : r1_xboole_0(k4_xboole_0(A_19,k2_xboole_0(B_20,C_21)),C_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_42811])).

tff(c_65072,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_64776,c_42869])).

tff(c_65249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_65072])).

tff(c_65250,plain,(
    r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_51])).

tff(c_65407,plain,(
    ! [A_1206,B_1207,C_1208] :
      ( ~ r1_xboole_0(A_1206,B_1207)
      | ~ r2_hidden(C_1208,B_1207)
      | ~ r2_hidden(C_1208,A_1206) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_65424,plain,(
    ! [C_1208] :
      ( ~ r2_hidden(C_1208,k2_xboole_0('#skF_6','#skF_5'))
      | ~ r2_hidden(C_1208,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_65250,c_65407])).

tff(c_87700,plain,(
    ! [A_1668] :
      ( ~ r2_hidden('#skF_2'(A_1668,k2_xboole_0('#skF_6','#skF_5'),A_1668),'#skF_4')
      | k4_xboole_0(A_1668,k2_xboole_0('#skF_6','#skF_5')) = A_1668 ) ),
    inference(resolution,[status(thm)],[c_86760,c_65424])).

tff(c_87709,plain,(
    k4_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_66128,c_87700])).

tff(c_65283,plain,(
    ! [A_1191,B_1192] :
      ( r2_hidden('#skF_3'(A_1191,B_1192),B_1192)
      | r1_xboole_0(A_1191,B_1192) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_71042,plain,(
    ! [A_1355,A_1356,B_1357] :
      ( ~ r2_hidden('#skF_3'(A_1355,k4_xboole_0(A_1356,B_1357)),B_1357)
      | r1_xboole_0(A_1355,k4_xboole_0(A_1356,B_1357)) ) ),
    inference(resolution,[status(thm)],[c_65283,c_6])).

tff(c_71138,plain,(
    ! [A_1358,A_1359] : r1_xboole_0(A_1358,k4_xboole_0(A_1359,A_1358)) ),
    inference(resolution,[status(thm)],[c_32,c_71042])).

tff(c_71215,plain,(
    ! [A_1360,A_1361] : r1_xboole_0(k4_xboole_0(A_1360,A_1361),A_1361) ),
    inference(resolution,[status(thm)],[c_71138,c_26])).

tff(c_71273,plain,(
    ! [A_19,B_20,C_21] : r1_xboole_0(k4_xboole_0(A_19,k2_xboole_0(B_20,C_21)),C_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_71215])).

tff(c_87813,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_87709,c_71273])).

tff(c_87976,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_87813])).

tff(c_87977,plain,(
    r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_88041,plain,(
    ! [A_1673,B_1674,C_1675] :
      ( ~ r1_xboole_0(A_1673,B_1674)
      | ~ r2_hidden(C_1675,B_1674)
      | ~ r2_hidden(C_1675,A_1673) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_88051,plain,(
    ! [C_1675] :
      ( ~ r2_hidden(C_1675,k2_xboole_0('#skF_6','#skF_5'))
      | ~ r2_hidden(C_1675,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_87977,c_88041])).

tff(c_111345,plain,(
    ! [A_2138] :
      ( ~ r2_hidden('#skF_2'(A_2138,k2_xboole_0('#skF_6','#skF_5'),A_2138),'#skF_4')
      | k4_xboole_0(A_2138,k2_xboole_0('#skF_6','#skF_5')) = A_2138 ) ),
    inference(resolution,[status(thm)],[c_110891,c_88051])).

tff(c_111354,plain,(
    k4_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_89315,c_111345])).

tff(c_88011,plain,(
    ! [A_1669,B_1670] :
      ( r2_hidden('#skF_3'(A_1669,B_1670),A_1669)
      | r1_xboole_0(A_1669,B_1670) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_92963,plain,(
    ! [A_1819,B_1820,B_1821] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_1819,B_1820),B_1821),B_1820)
      | r1_xboole_0(k4_xboole_0(A_1819,B_1820),B_1821) ) ),
    inference(resolution,[status(thm)],[c_88011,c_6])).

tff(c_93048,plain,(
    ! [A_1822,B_1823] : r1_xboole_0(k4_xboole_0(A_1822,B_1823),B_1823) ),
    inference(resolution,[status(thm)],[c_30,c_92963])).

tff(c_93995,plain,(
    ! [A_1845,B_1846,C_1847] : r1_xboole_0(k4_xboole_0(A_1845,k2_xboole_0(B_1846,C_1847)),C_1847) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_93048])).

tff(c_104765,plain,(
    ! [A_2060,B_2061,C_2062] : k3_xboole_0(k4_xboole_0(A_2060,k2_xboole_0(B_2061,C_2062)),C_2062) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_93995,c_22])).

tff(c_164,plain,(
    ! [B_36,A_37] :
      ( k3_xboole_0(B_36,A_37) = k1_xboole_0
      | k3_xboole_0(A_37,B_36) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_154,c_22])).

tff(c_104968,plain,(
    ! [C_2062,A_2060,B_2061] : k3_xboole_0(C_2062,k4_xboole_0(A_2060,k2_xboole_0(B_2061,C_2062))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_104765,c_164])).

tff(c_111395,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_111354,c_104968])).

tff(c_111649,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_163,c_111395])).

tff(c_111651,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_24,plain,(
    ! [A_9,B_10] :
      ( r1_xboole_0(A_9,B_10)
      | k3_xboole_0(A_9,B_10) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_111650,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_6')
    | r1_xboole_0('#skF_7','#skF_9') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_111675,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_111650])).

tff(c_111679,plain,(
    k3_xboole_0('#skF_4','#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_111675])).

tff(c_221810,plain,(
    ! [A_4001,B_4002,C_4003] :
      ( ~ r2_hidden('#skF_1'(A_4001,B_4002,C_4003),C_4003)
      | r2_hidden('#skF_2'(A_4001,B_4002,C_4003),C_4003)
      | k4_xboole_0(A_4001,B_4002) = C_4003 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_221819,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_2'(A_3,B_4,A_3),A_3)
      | k4_xboole_0(A_3,B_4) = A_3 ) ),
    inference(resolution,[status(thm)],[c_20,c_221810])).

tff(c_222367,plain,(
    ! [A_4020,B_4021,C_4022] :
      ( r2_hidden('#skF_1'(A_4020,B_4021,C_4022),A_4020)
      | r2_hidden('#skF_2'(A_4020,B_4021,C_4022),B_4021)
      | ~ r2_hidden('#skF_2'(A_4020,B_4021,C_4022),A_4020)
      | k4_xboole_0(A_4020,B_4021) = C_4022 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_233790,plain,(
    ! [A_4223,B_4224] :
      ( r2_hidden('#skF_2'(A_4223,B_4224,A_4223),B_4224)
      | ~ r2_hidden('#skF_2'(A_4223,B_4224,A_4223),A_4223)
      | k4_xboole_0(A_4223,B_4224) = A_4223 ) ),
    inference(resolution,[status(thm)],[c_222367,c_10])).

tff(c_247177,plain,(
    ! [A_4472,B_4473] :
      ( r2_hidden('#skF_2'(A_4472,B_4473,A_4472),B_4473)
      | k4_xboole_0(A_4472,B_4473) = A_4472 ) ),
    inference(resolution,[status(thm)],[c_221819,c_233790])).

tff(c_194222,plain,(
    ! [A_3460,B_3461,C_3462] :
      ( r2_hidden('#skF_1'(A_3460,B_3461,C_3462),A_3460)
      | r2_hidden('#skF_2'(A_3460,B_3461,C_3462),C_3462)
      | k4_xboole_0(A_3460,B_3461) = C_3462 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_194282,plain,(
    ! [A_3460,B_3461] :
      ( r2_hidden('#skF_2'(A_3460,B_3461,A_3460),A_3460)
      | k4_xboole_0(A_3460,B_3461) = A_3460 ) ),
    inference(resolution,[status(thm)],[c_194222,c_16])).

tff(c_194707,plain,(
    ! [A_3476,B_3477,C_3478] :
      ( ~ r2_hidden('#skF_1'(A_3476,B_3477,C_3478),C_3478)
      | r2_hidden('#skF_2'(A_3476,B_3477,C_3478),B_3477)
      | ~ r2_hidden('#skF_2'(A_3476,B_3477,C_3478),A_3476)
      | k4_xboole_0(A_3476,B_3477) = C_3478 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_203780,plain,(
    ! [A_3650,B_3651] :
      ( r2_hidden('#skF_2'(A_3650,B_3651,A_3650),B_3651)
      | ~ r2_hidden('#skF_2'(A_3650,B_3651,A_3650),A_3650)
      | k4_xboole_0(A_3650,B_3651) = A_3650 ) ),
    inference(resolution,[status(thm)],[c_14,c_194707])).

tff(c_218703,plain,(
    ! [A_3926,B_3927] :
      ( r2_hidden('#skF_2'(A_3926,B_3927,A_3926),B_3927)
      | k4_xboole_0(A_3926,B_3927) = A_3926 ) ),
    inference(resolution,[status(thm)],[c_194282,c_203780])).

tff(c_111680,plain,(
    ! [B_2139,A_2140] :
      ( r1_xboole_0(B_2139,A_2140)
      | k3_xboole_0(A_2140,B_2139) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_97,c_26])).

tff(c_111689,plain,(
    k3_xboole_0('#skF_6','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_111680,c_111675])).

tff(c_167052,plain,(
    ! [A_2974,B_2975,C_2976] :
      ( ~ r2_hidden('#skF_1'(A_2974,B_2975,C_2976),C_2976)
      | r2_hidden('#skF_2'(A_2974,B_2975,C_2976),C_2976)
      | k4_xboole_0(A_2974,B_2975) = C_2976 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_167061,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_2'(A_3,B_4,A_3),A_3)
      | k4_xboole_0(A_3,B_4) = A_3 ) ),
    inference(resolution,[status(thm)],[c_20,c_167052])).

tff(c_167240,plain,(
    ! [A_2992,B_2993,C_2994] :
      ( r2_hidden('#skF_1'(A_2992,B_2993,C_2994),A_2992)
      | r2_hidden('#skF_2'(A_2992,B_2993,C_2994),B_2993)
      | ~ r2_hidden('#skF_2'(A_2992,B_2993,C_2994),A_2992)
      | k4_xboole_0(A_2992,B_2993) = C_2994 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_176621,plain,(
    ! [A_3164,B_3165] :
      ( r2_hidden('#skF_2'(A_3164,B_3165,A_3164),B_3165)
      | ~ r2_hidden('#skF_2'(A_3164,B_3165,A_3164),A_3164)
      | k4_xboole_0(A_3164,B_3165) = A_3164 ) ),
    inference(resolution,[status(thm)],[c_167240,c_10])).

tff(c_190775,plain,(
    ! [A_3391,B_3392] :
      ( r2_hidden('#skF_2'(A_3391,B_3392,A_3391),B_3392)
      | k4_xboole_0(A_3391,B_3392) = A_3391 ) ),
    inference(resolution,[status(thm)],[c_167061,c_176621])).

tff(c_111694,plain,(
    r1_xboole_0('#skF_7','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_111700,plain,(
    k3_xboole_0('#skF_7','#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_111694,c_22])).

tff(c_112675,plain,(
    ! [A_2208,B_2209,C_2210] :
      ( r2_hidden('#skF_1'(A_2208,B_2209,C_2210),A_2208)
      | r2_hidden('#skF_2'(A_2208,B_2209,C_2210),C_2210)
      | k4_xboole_0(A_2208,B_2209) = C_2210 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_112733,plain,(
    ! [A_2208,B_2209] :
      ( r2_hidden('#skF_2'(A_2208,B_2209,A_2208),A_2208)
      | k4_xboole_0(A_2208,B_2209) = A_2208 ) ),
    inference(resolution,[status(thm)],[c_112675,c_16])).

tff(c_113273,plain,(
    ! [A_2232,B_2233,C_2234] :
      ( r2_hidden('#skF_1'(A_2232,B_2233,C_2234),A_2232)
      | r2_hidden('#skF_2'(A_2232,B_2233,C_2234),B_2233)
      | ~ r2_hidden('#skF_2'(A_2232,B_2233,C_2234),A_2232)
      | k4_xboole_0(A_2232,B_2233) = C_2234 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_122915,plain,(
    ! [A_2411,B_2412] :
      ( r2_hidden('#skF_2'(A_2411,B_2412,A_2411),B_2412)
      | ~ r2_hidden('#skF_2'(A_2411,B_2412,A_2411),A_2411)
      | k4_xboole_0(A_2411,B_2412) = A_2411 ) ),
    inference(resolution,[status(thm)],[c_113273,c_10])).

tff(c_139087,plain,(
    ! [A_2678,B_2679] :
      ( r2_hidden('#skF_2'(A_2678,B_2679,A_2678),B_2679)
      | k4_xboole_0(A_2678,B_2679) = A_2678 ) ),
    inference(resolution,[status(thm)],[c_112733,c_122915])).

tff(c_114103,plain,(
    ! [A_2261,B_2262] :
      ( r2_hidden('#skF_2'(A_2261,B_2262,A_2261),A_2261)
      | k4_xboole_0(A_2261,B_2262) = A_2261 ) ),
    inference(resolution,[status(thm)],[c_112675,c_16])).

tff(c_111741,plain,(
    r1_xboole_0('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_51])).

tff(c_111858,plain,(
    ! [A_2158,B_2159,C_2160] :
      ( ~ r1_xboole_0(A_2158,B_2159)
      | ~ r2_hidden(C_2160,B_2159)
      | ~ r2_hidden(C_2160,A_2158) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_111876,plain,(
    ! [C_2160] :
      ( ~ r2_hidden(C_2160,'#skF_8')
      | ~ r2_hidden(C_2160,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_111741,c_111858])).

tff(c_114153,plain,(
    ! [B_2262] :
      ( ~ r2_hidden('#skF_2'('#skF_7',B_2262,'#skF_7'),'#skF_8')
      | k4_xboole_0('#skF_7',B_2262) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_114103,c_111876])).

tff(c_139192,plain,(
    k4_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_139087,c_114153])).

tff(c_38,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k4_xboole_0(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_111949,plain,(
    ! [A_2167,B_2168,C_2169] : k4_xboole_0(k4_xboole_0(A_2167,B_2168),C_2169) = k4_xboole_0(A_2167,k2_xboole_0(B_2168,C_2169)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_111968,plain,(
    ! [A_2167,B_2168,C_2169] : k4_xboole_0(k4_xboole_0(A_2167,B_2168),k4_xboole_0(A_2167,k2_xboole_0(B_2168,C_2169))) = k3_xboole_0(k4_xboole_0(A_2167,B_2168),C_2169) ),
    inference(superposition,[status(thm),theory(equality)],[c_111949,c_38])).

tff(c_139957,plain,(
    ! [C_2169] : k4_xboole_0('#skF_7',k4_xboole_0('#skF_7',k2_xboole_0('#skF_8',C_2169))) = k3_xboole_0(k4_xboole_0('#skF_7','#skF_8'),C_2169) ),
    inference(superposition,[status(thm),theory(equality)],[c_139192,c_111968])).

tff(c_140084,plain,(
    ! [C_2169] : k3_xboole_0('#skF_7',k2_xboole_0('#skF_8',C_2169)) = k3_xboole_0('#skF_7',C_2169) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139192,c_38,c_139957])).

tff(c_111838,plain,(
    ~ r1_xboole_0('#skF_7',k2_xboole_0('#skF_8','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_53])).

tff(c_111846,plain,(
    k3_xboole_0('#skF_7',k2_xboole_0('#skF_8','#skF_9')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_111838])).

tff(c_166043,plain,(
    k3_xboole_0('#skF_7','#skF_9') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_140084,c_111846])).

tff(c_166046,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_111700,c_166043])).

tff(c_166047,plain,(
    r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_166093,plain,(
    ! [A_2925,B_2926,C_2927] :
      ( ~ r1_xboole_0(A_2925,B_2926)
      | ~ r2_hidden(C_2927,B_2926)
      | ~ r2_hidden(C_2927,A_2925) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_166121,plain,(
    ! [C_2927] :
      ( ~ r2_hidden(C_2927,k2_xboole_0('#skF_6','#skF_5'))
      | ~ r2_hidden(C_2927,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_166047,c_166093])).

tff(c_193030,plain,(
    ! [A_3404] :
      ( ~ r2_hidden('#skF_2'(A_3404,k2_xboole_0('#skF_6','#skF_5'),A_3404),'#skF_4')
      | k4_xboole_0(A_3404,k2_xboole_0('#skF_6','#skF_5')) = A_3404 ) ),
    inference(resolution,[status(thm)],[c_190775,c_166121])).

tff(c_193039,plain,(
    k4_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_167061,c_193030])).

tff(c_111780,plain,(
    ! [A_2151,B_2152] :
      ( r2_hidden('#skF_3'(A_2151,B_2152),B_2152)
      | r1_xboole_0(A_2151,B_2152) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_171089,plain,(
    ! [A_3075,A_3076,B_3077] :
      ( ~ r2_hidden('#skF_3'(A_3075,k4_xboole_0(A_3076,B_3077)),B_3077)
      | r1_xboole_0(A_3075,k4_xboole_0(A_3076,B_3077)) ) ),
    inference(resolution,[status(thm)],[c_111780,c_6])).

tff(c_171186,plain,(
    ! [A_3078,A_3079] : r1_xboole_0(A_3078,k4_xboole_0(A_3079,A_3078)) ),
    inference(resolution,[status(thm)],[c_32,c_171089])).

tff(c_184234,plain,(
    ! [C_3284,A_3285,B_3286] : r1_xboole_0(C_3284,k4_xboole_0(A_3285,k2_xboole_0(B_3286,C_3284))) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_171186])).

tff(c_184306,plain,(
    ! [B_2,A_3285,A_1] : r1_xboole_0(B_2,k4_xboole_0(A_3285,k2_xboole_0(B_2,A_1))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_184234])).

tff(c_193058,plain,(
    r1_xboole_0('#skF_6','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_193039,c_184306])).

tff(c_193318,plain,(
    k3_xboole_0('#skF_6','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_193058,c_22])).

tff(c_193325,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111689,c_193318])).

tff(c_193326,plain,(
    r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_51])).

tff(c_193433,plain,(
    ! [A_3413,B_3414,C_3415] :
      ( ~ r1_xboole_0(A_3413,B_3414)
      | ~ r2_hidden(C_3415,B_3414)
      | ~ r2_hidden(C_3415,A_3413) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_193451,plain,(
    ! [C_3415] :
      ( ~ r2_hidden(C_3415,k2_xboole_0('#skF_6','#skF_5'))
      | ~ r2_hidden(C_3415,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_193326,c_193433])).

tff(c_220243,plain,(
    ! [A_3933] :
      ( ~ r2_hidden('#skF_2'(A_3933,k2_xboole_0('#skF_6','#skF_5'),A_3933),'#skF_4')
      | k4_xboole_0(A_3933,k2_xboole_0('#skF_6','#skF_5')) = A_3933 ) ),
    inference(resolution,[status(thm)],[c_218703,c_193451])).

tff(c_220252,plain,(
    k4_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_194282,c_220243])).

tff(c_193375,plain,(
    ! [A_3407,B_3408] :
      ( r2_hidden('#skF_3'(A_3407,B_3408),B_3408)
      | r1_xboole_0(A_3407,B_3408) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_197698,plain,(
    ! [A_3553,A_3554,B_3555] :
      ( ~ r2_hidden('#skF_3'(A_3553,k4_xboole_0(A_3554,B_3555)),B_3555)
      | r1_xboole_0(A_3553,k4_xboole_0(A_3554,B_3555)) ) ),
    inference(resolution,[status(thm)],[c_193375,c_6])).

tff(c_197791,plain,(
    ! [A_3556,A_3557] : r1_xboole_0(A_3556,k4_xboole_0(A_3557,A_3556)) ),
    inference(resolution,[status(thm)],[c_32,c_197698])).

tff(c_205761,plain,(
    ! [C_3686,A_3687,B_3688] : r1_xboole_0(C_3686,k4_xboole_0(A_3687,k2_xboole_0(B_3688,C_3686))) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_197791])).

tff(c_211531,plain,(
    ! [A_3783,B_3784,C_3785] : r1_xboole_0(k4_xboole_0(A_3783,k2_xboole_0(B_3784,C_3785)),C_3785) ),
    inference(resolution,[status(thm)],[c_205761,c_26])).

tff(c_211603,plain,(
    ! [A_3783,B_2,A_1] : r1_xboole_0(k4_xboole_0(A_3783,k2_xboole_0(B_2,A_1)),B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_211531])).

tff(c_220630,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_220252,c_211603])).

tff(c_220840,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111675,c_220630])).

tff(c_220841,plain,(
    r1_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_220976,plain,(
    ! [A_3955,B_3956,C_3957] :
      ( ~ r1_xboole_0(A_3955,B_3956)
      | ~ r2_hidden(C_3957,B_3956)
      | ~ r2_hidden(C_3957,A_3955) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_220990,plain,(
    ! [C_3957] :
      ( ~ r2_hidden(C_3957,k2_xboole_0('#skF_6','#skF_5'))
      | ~ r2_hidden(C_3957,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_220841,c_220976])).

tff(c_248033,plain,(
    ! [A_4475] :
      ( ~ r2_hidden('#skF_2'(A_4475,k2_xboole_0('#skF_6','#skF_5'),A_4475),'#skF_4')
      | k4_xboole_0(A_4475,k2_xboole_0('#skF_6','#skF_5')) = A_4475 ) ),
    inference(resolution,[status(thm)],[c_247177,c_220990])).

tff(c_248042,plain,(
    k4_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_221819,c_248033])).

tff(c_220897,plain,(
    ! [A_3945,B_3946] :
      ( r2_hidden('#skF_3'(A_3945,B_3946),A_3945)
      | r1_xboole_0(A_3945,B_3946) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_226882,plain,(
    ! [A_4114,B_4115,B_4116] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_4114,B_4115),B_4116),B_4115)
      | r1_xboole_0(k4_xboole_0(A_4114,B_4115),B_4116) ) ),
    inference(resolution,[status(thm)],[c_220897,c_6])).

tff(c_226981,plain,(
    ! [A_4117,B_4118] : r1_xboole_0(k4_xboole_0(A_4117,B_4118),B_4118) ),
    inference(resolution,[status(thm)],[c_30,c_226882])).

tff(c_227297,plain,(
    ! [A_4127,B_4128] : k3_xboole_0(k4_xboole_0(A_4127,B_4128),B_4128) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_226981,c_22])).

tff(c_242741,plain,(
    ! [A_4424,B_4425,C_4426] : k3_xboole_0(k4_xboole_0(A_4424,k2_xboole_0(B_4425,C_4426)),C_4426) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_227297])).

tff(c_242931,plain,(
    ! [A_4424,A_1,B_2] : k3_xboole_0(k4_xboole_0(A_4424,k2_xboole_0(A_1,B_2)),A_1) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_242741])).

tff(c_248054,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_248042,c_242931])).

tff(c_248330,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111679,c_248054])).

tff(c_248332,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_111650])).

tff(c_50,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_6')
    | ~ r1_xboole_0('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_7',k2_xboole_0('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_248415,plain,(
    ~ r1_xboole_0('#skF_7',k2_xboole_0('#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111651,c_248332,c_50])).

tff(c_249317,plain,(
    ! [A_4544,B_4545,C_4546] :
      ( r2_hidden('#skF_1'(A_4544,B_4545,C_4546),A_4544)
      | r2_hidden('#skF_2'(A_4544,B_4545,C_4546),C_4546)
      | k4_xboole_0(A_4544,B_4545) = C_4546 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_249381,plain,(
    ! [A_4544,B_4545] :
      ( r2_hidden('#skF_2'(A_4544,B_4545,A_4544),A_4544)
      | k4_xboole_0(A_4544,B_4545) = A_4544 ) ),
    inference(resolution,[status(thm)],[c_249317,c_16])).

tff(c_249564,plain,(
    ! [A_4558,B_4559,C_4560] :
      ( ~ r2_hidden('#skF_1'(A_4558,B_4559,C_4560),C_4560)
      | r2_hidden('#skF_2'(A_4558,B_4559,C_4560),B_4559)
      | ~ r2_hidden('#skF_2'(A_4558,B_4559,C_4560),A_4558)
      | k4_xboole_0(A_4558,B_4559) = C_4560 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_258800,plain,(
    ! [A_4746,B_4747] :
      ( r2_hidden('#skF_2'(A_4746,B_4747,A_4746),B_4747)
      | ~ r2_hidden('#skF_2'(A_4746,B_4747,A_4746),A_4746)
      | k4_xboole_0(A_4746,B_4747) = A_4746 ) ),
    inference(resolution,[status(thm)],[c_14,c_249564])).

tff(c_277530,plain,(
    ! [A_5024,B_5025] :
      ( r2_hidden('#skF_2'(A_5024,B_5025,A_5024),B_5025)
      | k4_xboole_0(A_5024,B_5025) = A_5024 ) ),
    inference(resolution,[status(thm)],[c_249381,c_258800])).

tff(c_250845,plain,(
    ! [A_4600,B_4601] :
      ( r2_hidden('#skF_2'(A_4600,B_4601,A_4600),A_4600)
      | k4_xboole_0(A_4600,B_4601) = A_4600 ) ),
    inference(resolution,[status(thm)],[c_249317,c_16])).

tff(c_248347,plain,(
    r1_xboole_0('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_51])).

tff(c_248557,plain,(
    ! [A_4497,B_4498,C_4499] :
      ( ~ r1_xboole_0(A_4497,B_4498)
      | ~ r2_hidden(C_4499,B_4498)
      | ~ r2_hidden(C_4499,A_4497) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_248582,plain,(
    ! [C_4499] :
      ( ~ r2_hidden(C_4499,'#skF_8')
      | ~ r2_hidden(C_4499,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_248347,c_248557])).

tff(c_250890,plain,(
    ! [B_4601] :
      ( ~ r2_hidden('#skF_2'('#skF_7',B_4601,'#skF_7'),'#skF_8')
      | k4_xboole_0('#skF_7',B_4601) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_250845,c_248582])).

tff(c_277643,plain,(
    k4_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_277530,c_250890])).

tff(c_248331,plain,(
    r1_xboole_0('#skF_7','#skF_9') ),
    inference(splitRight,[status(thm)],[c_111650])).

tff(c_248584,plain,(
    ! [C_4499] :
      ( ~ r2_hidden(C_4499,'#skF_9')
      | ~ r2_hidden(C_4499,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_248331,c_248557])).

tff(c_250892,plain,(
    ! [B_4601] :
      ( ~ r2_hidden('#skF_2'('#skF_7',B_4601,'#skF_7'),'#skF_9')
      | k4_xboole_0('#skF_7',B_4601) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_250845,c_248584])).

tff(c_277646,plain,(
    k4_xboole_0('#skF_7','#skF_9') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_277530,c_250892])).

tff(c_317364,plain,(
    ! [C_5404] : k4_xboole_0('#skF_7',k2_xboole_0('#skF_9',C_5404)) = k4_xboole_0('#skF_7',C_5404) ),
    inference(superposition,[status(thm),theory(equality)],[c_277646,c_36])).

tff(c_248444,plain,(
    ! [A_4485,B_4486] :
      ( r2_hidden('#skF_3'(A_4485,B_4486),B_4486)
      | r1_xboole_0(A_4485,B_4486) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_252554,plain,(
    ! [A_4639,A_4640,B_4641] :
      ( ~ r2_hidden('#skF_3'(A_4639,k4_xboole_0(A_4640,B_4641)),B_4641)
      | r1_xboole_0(A_4639,k4_xboole_0(A_4640,B_4641)) ) ),
    inference(resolution,[status(thm)],[c_248444,c_6])).

tff(c_252638,plain,(
    ! [A_4642,A_4643] : r1_xboole_0(A_4642,k4_xboole_0(A_4643,A_4642)) ),
    inference(resolution,[status(thm)],[c_32,c_252554])).

tff(c_252699,plain,(
    ! [A_4643,A_4642] : r1_xboole_0(k4_xboole_0(A_4643,A_4642),A_4642) ),
    inference(resolution,[status(thm)],[c_252638,c_26])).

tff(c_317901,plain,(
    ! [C_5405] : r1_xboole_0(k4_xboole_0('#skF_7',C_5405),k2_xboole_0('#skF_9',C_5405)) ),
    inference(superposition,[status(thm),theory(equality)],[c_317364,c_252699])).

tff(c_317958,plain,(
    r1_xboole_0('#skF_7',k2_xboole_0('#skF_9','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_277643,c_317901])).

tff(c_318029,plain,(
    r1_xboole_0('#skF_7',k2_xboole_0('#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_317958])).

tff(c_318031,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_248415,c_318029])).

tff(c_318033,plain,(
    ~ r1_xboole_0('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_51])).

tff(c_46,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_6')
    | ~ r1_xboole_0('#skF_4','#skF_5')
    | r1_xboole_0('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_318070,plain,(
    r1_xboole_0('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111651,c_248332,c_46])).

tff(c_318071,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_318033,c_318070])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:49:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 53.65/42.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 53.65/42.81  
% 53.65/42.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 53.65/42.81  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4
% 53.65/42.81  
% 53.65/42.81  %Foreground sorts:
% 53.65/42.81  
% 53.65/42.81  
% 53.65/42.81  %Background operators:
% 53.65/42.81  
% 53.65/42.81  
% 53.65/42.81  %Foreground operators:
% 53.65/42.81  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 53.65/42.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 53.65/42.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 53.65/42.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 53.65/42.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 53.65/42.81  tff('#skF_7', type, '#skF_7': $i).
% 53.65/42.81  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 53.65/42.81  tff('#skF_5', type, '#skF_5': $i).
% 53.65/42.81  tff('#skF_6', type, '#skF_6': $i).
% 53.65/42.81  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 53.65/42.81  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 53.65/42.81  tff('#skF_9', type, '#skF_9': $i).
% 53.65/42.81  tff('#skF_8', type, '#skF_8': $i).
% 53.65/42.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 53.65/42.81  tff('#skF_4', type, '#skF_4': $i).
% 53.65/42.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 53.65/42.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 53.65/42.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 53.65/42.81  
% 53.88/42.85  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 53.88/42.85  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 53.88/42.85  tff(f_86, negated_conjecture, ~(![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 53.88/42.85  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 53.88/42.85  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 53.88/42.85  tff(f_63, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 53.88/42.85  tff(f_67, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 53.88/42.85  tff(f_69, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 53.88/42.85  tff(c_97, plain, (![A_29, B_30]: (r1_xboole_0(A_29, B_30) | k3_xboole_0(A_29, B_30)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 53.88/42.85  tff(c_26, plain, (![B_12, A_11]: (r1_xboole_0(B_12, A_11) | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 53.88/42.85  tff(c_154, plain, (![B_36, A_37]: (r1_xboole_0(B_36, A_37) | k3_xboole_0(A_37, B_36)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_97, c_26])).
% 53.88/42.85  tff(c_42, plain, (~r1_xboole_0('#skF_4', '#skF_6') | ~r1_xboole_0('#skF_4', '#skF_5') | r1_xboole_0('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_86])).
% 53.88/42.85  tff(c_149, plain, (~r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_42])).
% 53.88/42.85  tff(c_163, plain, (k3_xboole_0('#skF_5', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_154, c_149])).
% 53.88/42.85  tff(c_20, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), A_3) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 53.88/42.85  tff(c_89301, plain, (![A_1731, B_1732, C_1733]: (~r2_hidden('#skF_1'(A_1731, B_1732, C_1733), C_1733) | r2_hidden('#skF_2'(A_1731, B_1732, C_1733), C_1733) | k4_xboole_0(A_1731, B_1732)=C_1733)), inference(cnfTransformation, [status(thm)], [f_37])).
% 53.88/42.85  tff(c_89315, plain, (![A_3, B_4]: (r2_hidden('#skF_2'(A_3, B_4, A_3), A_3) | k4_xboole_0(A_3, B_4)=A_3)), inference(resolution, [status(thm)], [c_20, c_89301])).
% 53.88/42.85  tff(c_14, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), A_3) | r2_hidden('#skF_2'(A_3, B_4, C_5), B_4) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), A_3) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 53.88/42.85  tff(c_89930, plain, (![A_1752, B_1753, C_1754]: (~r2_hidden('#skF_1'(A_1752, B_1753, C_1754), C_1754) | r2_hidden('#skF_2'(A_1752, B_1753, C_1754), B_1753) | ~r2_hidden('#skF_2'(A_1752, B_1753, C_1754), A_1752) | k4_xboole_0(A_1752, B_1753)=C_1754)), inference(cnfTransformation, [status(thm)], [f_37])).
% 53.88/42.85  tff(c_99905, plain, (![A_1958, B_1959]: (r2_hidden('#skF_2'(A_1958, B_1959, A_1958), B_1959) | ~r2_hidden('#skF_2'(A_1958, B_1959, A_1958), A_1958) | k4_xboole_0(A_1958, B_1959)=A_1958)), inference(resolution, [status(thm)], [c_14, c_89930])).
% 53.88/42.85  tff(c_110891, plain, (![A_2136, B_2137]: (r2_hidden('#skF_2'(A_2136, B_2137, A_2136), B_2137) | k4_xboole_0(A_2136, B_2137)=A_2136)), inference(resolution, [status(thm)], [c_89315, c_99905])).
% 53.88/42.85  tff(c_66077, plain, (![A_1241, B_1242, C_1243]: (r2_hidden('#skF_1'(A_1241, B_1242, C_1243), A_1241) | r2_hidden('#skF_2'(A_1241, B_1242, C_1243), C_1243) | k4_xboole_0(A_1241, B_1242)=C_1243)), inference(cnfTransformation, [status(thm)], [f_37])).
% 53.88/42.85  tff(c_16, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 53.88/42.85  tff(c_66128, plain, (![A_1241, B_1242]: (r2_hidden('#skF_2'(A_1241, B_1242, A_1241), A_1241) | k4_xboole_0(A_1241, B_1242)=A_1241)), inference(resolution, [status(thm)], [c_66077, c_16])).
% 53.88/42.85  tff(c_67279, plain, (![A_1282, B_1283, C_1284]: (~r2_hidden('#skF_1'(A_1282, B_1283, C_1284), C_1284) | r2_hidden('#skF_2'(A_1282, B_1283, C_1284), B_1283) | ~r2_hidden('#skF_2'(A_1282, B_1283, C_1284), A_1282) | k4_xboole_0(A_1282, B_1283)=C_1284)), inference(cnfTransformation, [status(thm)], [f_37])).
% 53.88/42.85  tff(c_78409, plain, (![A_1465, B_1466]: (r2_hidden('#skF_2'(A_1465, B_1466, A_1465), B_1466) | ~r2_hidden('#skF_2'(A_1465, B_1466, A_1465), A_1465) | k4_xboole_0(A_1465, B_1466)=A_1465)), inference(resolution, [status(thm)], [c_14, c_67279])).
% 53.88/42.85  tff(c_86760, plain, (![A_1662, B_1663]: (r2_hidden('#skF_2'(A_1662, B_1663, A_1662), B_1663) | k4_xboole_0(A_1662, B_1663)=A_1662)), inference(resolution, [status(thm)], [c_66128, c_78409])).
% 53.88/42.85  tff(c_38133, plain, (![A_710, B_711, C_712]: (~r2_hidden('#skF_1'(A_710, B_711, C_712), C_712) | r2_hidden('#skF_2'(A_710, B_711, C_712), C_712) | k4_xboole_0(A_710, B_711)=C_712)), inference(cnfTransformation, [status(thm)], [f_37])).
% 53.88/42.85  tff(c_38142, plain, (![A_3, B_4]: (r2_hidden('#skF_2'(A_3, B_4, A_3), A_3) | k4_xboole_0(A_3, B_4)=A_3)), inference(resolution, [status(thm)], [c_20, c_38133])).
% 53.88/42.85  tff(c_38721, plain, (![A_732, B_733, C_734]: (~r2_hidden('#skF_1'(A_732, B_733, C_734), C_734) | r2_hidden('#skF_2'(A_732, B_733, C_734), B_733) | ~r2_hidden('#skF_2'(A_732, B_733, C_734), A_732) | k4_xboole_0(A_732, B_733)=C_734)), inference(cnfTransformation, [status(thm)], [f_37])).
% 53.88/42.85  tff(c_47495, plain, (![A_897, B_898]: (r2_hidden('#skF_2'(A_897, B_898, A_897), B_898) | ~r2_hidden('#skF_2'(A_897, B_898, A_897), A_897) | k4_xboole_0(A_897, B_898)=A_897)), inference(resolution, [status(thm)], [c_14, c_38721])).
% 53.88/42.85  tff(c_62781, plain, (![A_1175, B_1176]: (r2_hidden('#skF_2'(A_1175, B_1176, A_1175), B_1176) | k4_xboole_0(A_1175, B_1176)=A_1175)), inference(resolution, [status(thm)], [c_38142, c_47495])).
% 53.88/42.85  tff(c_100, plain, (![B_30, A_29]: (r1_xboole_0(B_30, A_29) | k3_xboole_0(A_29, B_30)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_97, c_26])).
% 53.88/42.85  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 53.88/42.85  tff(c_48, plain, (r1_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6')) | ~r1_xboole_0('#skF_7', k2_xboole_0('#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 53.88/42.85  tff(c_53, plain, (r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5')) | ~r1_xboole_0('#skF_7', k2_xboole_0('#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_48])).
% 53.88/42.85  tff(c_354, plain, (~r1_xboole_0('#skF_7', k2_xboole_0('#skF_8', '#skF_9'))), inference(splitLeft, [status(thm)], [c_53])).
% 53.88/42.85  tff(c_361, plain, (k3_xboole_0(k2_xboole_0('#skF_8', '#skF_9'), '#skF_7')!=k1_xboole_0), inference(resolution, [status(thm)], [c_100, c_354])).
% 53.88/42.85  tff(c_1020, plain, (![A_95, B_96, C_97]: (r2_hidden('#skF_1'(A_95, B_96, C_97), A_95) | r2_hidden('#skF_2'(A_95, B_96, C_97), C_97) | k4_xboole_0(A_95, B_96)=C_97)), inference(cnfTransformation, [status(thm)], [f_37])).
% 53.88/42.85  tff(c_1070, plain, (![A_95, B_96]: (r2_hidden('#skF_2'(A_95, B_96, A_95), A_95) | k4_xboole_0(A_95, B_96)=A_95)), inference(resolution, [status(thm)], [c_1020, c_16])).
% 53.88/42.85  tff(c_1381, plain, (![A_115, B_116, C_117]: (r2_hidden('#skF_1'(A_115, B_116, C_117), A_115) | r2_hidden('#skF_2'(A_115, B_116, C_117), B_116) | ~r2_hidden('#skF_2'(A_115, B_116, C_117), A_115) | k4_xboole_0(A_115, B_116)=C_117)), inference(cnfTransformation, [status(thm)], [f_37])).
% 53.88/42.85  tff(c_10, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | r2_hidden('#skF_2'(A_3, B_4, C_5), B_4) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), A_3) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 53.88/42.85  tff(c_11596, plain, (![A_300, B_301]: (r2_hidden('#skF_2'(A_300, B_301, A_300), B_301) | ~r2_hidden('#skF_2'(A_300, B_301, A_300), A_300) | k4_xboole_0(A_300, B_301)=A_300)), inference(resolution, [status(thm)], [c_1381, c_10])).
% 53.88/42.85  tff(c_23157, plain, (![A_515, B_516]: (r2_hidden('#skF_2'(A_515, B_516, A_515), B_516) | k4_xboole_0(A_515, B_516)=A_515)), inference(resolution, [status(thm)], [c_1070, c_11596])).
% 53.88/42.85  tff(c_3795, plain, (![A_169, B_170]: (r2_hidden('#skF_2'(A_169, B_170, A_169), A_169) | k4_xboole_0(A_169, B_170)=A_169)), inference(resolution, [status(thm)], [c_1020, c_16])).
% 53.88/42.85  tff(c_44, plain, (r1_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6')) | r1_xboole_0('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_86])).
% 53.88/42.85  tff(c_51, plain, (r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5')) | r1_xboole_0('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_44])).
% 53.88/42.85  tff(c_211, plain, (r1_xboole_0('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_51])).
% 53.88/42.85  tff(c_313, plain, (![A_55, B_56, C_57]: (~r1_xboole_0(A_55, B_56) | ~r2_hidden(C_57, B_56) | ~r2_hidden(C_57, A_55))), inference(cnfTransformation, [status(thm)], [f_63])).
% 53.88/42.85  tff(c_327, plain, (![C_57]: (~r2_hidden(C_57, '#skF_8') | ~r2_hidden(C_57, '#skF_7'))), inference(resolution, [status(thm)], [c_211, c_313])).
% 53.88/42.85  tff(c_3844, plain, (![B_170]: (~r2_hidden('#skF_2'('#skF_7', B_170, '#skF_7'), '#skF_8') | k4_xboole_0('#skF_7', B_170)='#skF_7')), inference(resolution, [status(thm)], [c_3795, c_327])).
% 53.88/42.85  tff(c_23244, plain, (k4_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_23157, c_3844])).
% 53.88/42.85  tff(c_40, plain, (r1_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6')) | r1_xboole_0('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_86])).
% 53.88/42.85  tff(c_52, plain, (r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5')) | r1_xboole_0('#skF_7', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_40])).
% 53.88/42.85  tff(c_187, plain, (r1_xboole_0('#skF_7', '#skF_9')), inference(splitLeft, [status(thm)], [c_52])).
% 53.88/42.85  tff(c_329, plain, (![C_57]: (~r2_hidden(C_57, '#skF_9') | ~r2_hidden(C_57, '#skF_7'))), inference(resolution, [status(thm)], [c_187, c_313])).
% 53.88/42.85  tff(c_3843, plain, (![B_170]: (~r2_hidden('#skF_2'('#skF_7', B_170, '#skF_7'), '#skF_9') | k4_xboole_0('#skF_7', B_170)='#skF_7')), inference(resolution, [status(thm)], [c_3795, c_329])).
% 53.88/42.85  tff(c_23242, plain, (k4_xboole_0('#skF_7', '#skF_9')='#skF_7'), inference(resolution, [status(thm)], [c_23157, c_3843])).
% 53.88/42.85  tff(c_36, plain, (![A_19, B_20, C_21]: (k4_xboole_0(k4_xboole_0(A_19, B_20), C_21)=k4_xboole_0(A_19, k2_xboole_0(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 53.88/42.85  tff(c_36584, plain, (![C_666]: (k4_xboole_0('#skF_7', k2_xboole_0('#skF_9', C_666))=k4_xboole_0('#skF_7', C_666))), inference(superposition, [status(thm), theory('equality')], [c_23242, c_36])).
% 53.88/42.85  tff(c_30, plain, (![A_13, B_14]: (r2_hidden('#skF_3'(A_13, B_14), B_14) | r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 53.88/42.85  tff(c_219, plain, (![A_46, B_47]: (r2_hidden('#skF_3'(A_46, B_47), A_46) | r1_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_63])).
% 53.88/42.85  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 53.88/42.85  tff(c_5318, plain, (![A_200, B_201, B_202]: (~r2_hidden('#skF_3'(k4_xboole_0(A_200, B_201), B_202), B_201) | r1_xboole_0(k4_xboole_0(A_200, B_201), B_202))), inference(resolution, [status(thm)], [c_219, c_6])).
% 53.88/42.85  tff(c_5412, plain, (![A_203, B_204]: (r1_xboole_0(k4_xboole_0(A_203, B_204), B_204))), inference(resolution, [status(thm)], [c_30, c_5318])).
% 53.88/42.85  tff(c_5482, plain, (![B_204, A_203]: (r1_xboole_0(B_204, k4_xboole_0(A_203, B_204)))), inference(resolution, [status(thm)], [c_5412, c_26])).
% 53.88/42.85  tff(c_37092, plain, (![C_667]: (r1_xboole_0(k2_xboole_0('#skF_9', C_667), k4_xboole_0('#skF_7', C_667)))), inference(superposition, [status(thm), theory('equality')], [c_36584, c_5482])).
% 53.88/42.85  tff(c_37117, plain, (r1_xboole_0(k2_xboole_0('#skF_9', '#skF_8'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_23244, c_37092])).
% 53.88/42.85  tff(c_37184, plain, (r1_xboole_0(k2_xboole_0('#skF_8', '#skF_9'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_37117])).
% 53.88/42.85  tff(c_22, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=k1_xboole_0 | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 53.88/42.85  tff(c_37204, plain, (k3_xboole_0(k2_xboole_0('#skF_8', '#skF_9'), '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_37184, c_22])).
% 53.88/42.85  tff(c_37211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_361, c_37204])).
% 53.88/42.85  tff(c_37212, plain, (r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitRight, [status(thm)], [c_53])).
% 53.88/42.85  tff(c_28, plain, (![A_13, B_14, C_17]: (~r1_xboole_0(A_13, B_14) | ~r2_hidden(C_17, B_14) | ~r2_hidden(C_17, A_13))), inference(cnfTransformation, [status(thm)], [f_63])).
% 53.88/42.85  tff(c_37221, plain, (![C_17]: (~r2_hidden(C_17, k2_xboole_0('#skF_6', '#skF_5')) | ~r2_hidden(C_17, '#skF_4'))), inference(resolution, [status(thm)], [c_37212, c_28])).
% 53.88/42.85  tff(c_64767, plain, (![A_1187]: (~r2_hidden('#skF_2'(A_1187, k2_xboole_0('#skF_6', '#skF_5'), A_1187), '#skF_4') | k4_xboole_0(A_1187, k2_xboole_0('#skF_6', '#skF_5'))=A_1187)), inference(resolution, [status(thm)], [c_62781, c_37221])).
% 53.88/42.85  tff(c_64776, plain, (k4_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))='#skF_4'), inference(resolution, [status(thm)], [c_38142, c_64767])).
% 53.88/42.85  tff(c_32, plain, (![A_13, B_14]: (r2_hidden('#skF_3'(A_13, B_14), A_13) | r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 53.88/42.85  tff(c_250, plain, (![A_48, B_49]: (r2_hidden('#skF_3'(A_48, B_49), B_49) | r1_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_63])).
% 53.88/42.85  tff(c_42644, plain, (![A_816, A_817, B_818]: (~r2_hidden('#skF_3'(A_816, k4_xboole_0(A_817, B_818)), B_818) | r1_xboole_0(A_816, k4_xboole_0(A_817, B_818)))), inference(resolution, [status(thm)], [c_250, c_6])).
% 53.88/42.85  tff(c_42737, plain, (![A_819, A_820]: (r1_xboole_0(A_819, k4_xboole_0(A_820, A_819)))), inference(resolution, [status(thm)], [c_32, c_42644])).
% 53.88/42.85  tff(c_42811, plain, (![A_821, A_822]: (r1_xboole_0(k4_xboole_0(A_821, A_822), A_822))), inference(resolution, [status(thm)], [c_42737, c_26])).
% 53.88/42.85  tff(c_42869, plain, (![A_19, B_20, C_21]: (r1_xboole_0(k4_xboole_0(A_19, k2_xboole_0(B_20, C_21)), C_21))), inference(superposition, [status(thm), theory('equality')], [c_36, c_42811])).
% 53.88/42.85  tff(c_65072, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_64776, c_42869])).
% 53.88/42.85  tff(c_65249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_149, c_65072])).
% 53.88/42.85  tff(c_65250, plain, (r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitRight, [status(thm)], [c_51])).
% 53.88/42.85  tff(c_65407, plain, (![A_1206, B_1207, C_1208]: (~r1_xboole_0(A_1206, B_1207) | ~r2_hidden(C_1208, B_1207) | ~r2_hidden(C_1208, A_1206))), inference(cnfTransformation, [status(thm)], [f_63])).
% 53.88/42.85  tff(c_65424, plain, (![C_1208]: (~r2_hidden(C_1208, k2_xboole_0('#skF_6', '#skF_5')) | ~r2_hidden(C_1208, '#skF_4'))), inference(resolution, [status(thm)], [c_65250, c_65407])).
% 53.88/42.85  tff(c_87700, plain, (![A_1668]: (~r2_hidden('#skF_2'(A_1668, k2_xboole_0('#skF_6', '#skF_5'), A_1668), '#skF_4') | k4_xboole_0(A_1668, k2_xboole_0('#skF_6', '#skF_5'))=A_1668)), inference(resolution, [status(thm)], [c_86760, c_65424])).
% 53.88/42.85  tff(c_87709, plain, (k4_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))='#skF_4'), inference(resolution, [status(thm)], [c_66128, c_87700])).
% 53.88/42.85  tff(c_65283, plain, (![A_1191, B_1192]: (r2_hidden('#skF_3'(A_1191, B_1192), B_1192) | r1_xboole_0(A_1191, B_1192))), inference(cnfTransformation, [status(thm)], [f_63])).
% 53.88/42.85  tff(c_71042, plain, (![A_1355, A_1356, B_1357]: (~r2_hidden('#skF_3'(A_1355, k4_xboole_0(A_1356, B_1357)), B_1357) | r1_xboole_0(A_1355, k4_xboole_0(A_1356, B_1357)))), inference(resolution, [status(thm)], [c_65283, c_6])).
% 53.88/42.85  tff(c_71138, plain, (![A_1358, A_1359]: (r1_xboole_0(A_1358, k4_xboole_0(A_1359, A_1358)))), inference(resolution, [status(thm)], [c_32, c_71042])).
% 53.88/42.85  tff(c_71215, plain, (![A_1360, A_1361]: (r1_xboole_0(k4_xboole_0(A_1360, A_1361), A_1361))), inference(resolution, [status(thm)], [c_71138, c_26])).
% 53.88/42.85  tff(c_71273, plain, (![A_19, B_20, C_21]: (r1_xboole_0(k4_xboole_0(A_19, k2_xboole_0(B_20, C_21)), C_21))), inference(superposition, [status(thm), theory('equality')], [c_36, c_71215])).
% 53.88/42.85  tff(c_87813, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_87709, c_71273])).
% 53.88/42.85  tff(c_87976, plain, $false, inference(negUnitSimplification, [status(thm)], [c_149, c_87813])).
% 53.88/42.85  tff(c_87977, plain, (r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitRight, [status(thm)], [c_52])).
% 53.88/42.85  tff(c_88041, plain, (![A_1673, B_1674, C_1675]: (~r1_xboole_0(A_1673, B_1674) | ~r2_hidden(C_1675, B_1674) | ~r2_hidden(C_1675, A_1673))), inference(cnfTransformation, [status(thm)], [f_63])).
% 53.88/42.85  tff(c_88051, plain, (![C_1675]: (~r2_hidden(C_1675, k2_xboole_0('#skF_6', '#skF_5')) | ~r2_hidden(C_1675, '#skF_4'))), inference(resolution, [status(thm)], [c_87977, c_88041])).
% 53.88/42.85  tff(c_111345, plain, (![A_2138]: (~r2_hidden('#skF_2'(A_2138, k2_xboole_0('#skF_6', '#skF_5'), A_2138), '#skF_4') | k4_xboole_0(A_2138, k2_xboole_0('#skF_6', '#skF_5'))=A_2138)), inference(resolution, [status(thm)], [c_110891, c_88051])).
% 53.88/42.85  tff(c_111354, plain, (k4_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))='#skF_4'), inference(resolution, [status(thm)], [c_89315, c_111345])).
% 53.88/42.85  tff(c_88011, plain, (![A_1669, B_1670]: (r2_hidden('#skF_3'(A_1669, B_1670), A_1669) | r1_xboole_0(A_1669, B_1670))), inference(cnfTransformation, [status(thm)], [f_63])).
% 53.88/42.85  tff(c_92963, plain, (![A_1819, B_1820, B_1821]: (~r2_hidden('#skF_3'(k4_xboole_0(A_1819, B_1820), B_1821), B_1820) | r1_xboole_0(k4_xboole_0(A_1819, B_1820), B_1821))), inference(resolution, [status(thm)], [c_88011, c_6])).
% 53.88/42.85  tff(c_93048, plain, (![A_1822, B_1823]: (r1_xboole_0(k4_xboole_0(A_1822, B_1823), B_1823))), inference(resolution, [status(thm)], [c_30, c_92963])).
% 53.88/42.85  tff(c_93995, plain, (![A_1845, B_1846, C_1847]: (r1_xboole_0(k4_xboole_0(A_1845, k2_xboole_0(B_1846, C_1847)), C_1847))), inference(superposition, [status(thm), theory('equality')], [c_36, c_93048])).
% 53.88/42.85  tff(c_104765, plain, (![A_2060, B_2061, C_2062]: (k3_xboole_0(k4_xboole_0(A_2060, k2_xboole_0(B_2061, C_2062)), C_2062)=k1_xboole_0)), inference(resolution, [status(thm)], [c_93995, c_22])).
% 53.88/42.85  tff(c_164, plain, (![B_36, A_37]: (k3_xboole_0(B_36, A_37)=k1_xboole_0 | k3_xboole_0(A_37, B_36)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_154, c_22])).
% 53.88/42.85  tff(c_104968, plain, (![C_2062, A_2060, B_2061]: (k3_xboole_0(C_2062, k4_xboole_0(A_2060, k2_xboole_0(B_2061, C_2062)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_104765, c_164])).
% 53.88/42.85  tff(c_111395, plain, (k3_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_111354, c_104968])).
% 53.88/42.85  tff(c_111649, plain, $false, inference(negUnitSimplification, [status(thm)], [c_163, c_111395])).
% 53.88/42.85  tff(c_111651, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_42])).
% 53.88/42.85  tff(c_24, plain, (![A_9, B_10]: (r1_xboole_0(A_9, B_10) | k3_xboole_0(A_9, B_10)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 53.88/42.85  tff(c_111650, plain, (~r1_xboole_0('#skF_4', '#skF_6') | r1_xboole_0('#skF_7', '#skF_9')), inference(splitRight, [status(thm)], [c_42])).
% 53.88/42.85  tff(c_111675, plain, (~r1_xboole_0('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_111650])).
% 53.88/42.85  tff(c_111679, plain, (k3_xboole_0('#skF_4', '#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_111675])).
% 53.88/42.85  tff(c_221810, plain, (![A_4001, B_4002, C_4003]: (~r2_hidden('#skF_1'(A_4001, B_4002, C_4003), C_4003) | r2_hidden('#skF_2'(A_4001, B_4002, C_4003), C_4003) | k4_xboole_0(A_4001, B_4002)=C_4003)), inference(cnfTransformation, [status(thm)], [f_37])).
% 53.88/42.85  tff(c_221819, plain, (![A_3, B_4]: (r2_hidden('#skF_2'(A_3, B_4, A_3), A_3) | k4_xboole_0(A_3, B_4)=A_3)), inference(resolution, [status(thm)], [c_20, c_221810])).
% 53.88/42.85  tff(c_222367, plain, (![A_4020, B_4021, C_4022]: (r2_hidden('#skF_1'(A_4020, B_4021, C_4022), A_4020) | r2_hidden('#skF_2'(A_4020, B_4021, C_4022), B_4021) | ~r2_hidden('#skF_2'(A_4020, B_4021, C_4022), A_4020) | k4_xboole_0(A_4020, B_4021)=C_4022)), inference(cnfTransformation, [status(thm)], [f_37])).
% 53.88/42.85  tff(c_233790, plain, (![A_4223, B_4224]: (r2_hidden('#skF_2'(A_4223, B_4224, A_4223), B_4224) | ~r2_hidden('#skF_2'(A_4223, B_4224, A_4223), A_4223) | k4_xboole_0(A_4223, B_4224)=A_4223)), inference(resolution, [status(thm)], [c_222367, c_10])).
% 53.88/42.85  tff(c_247177, plain, (![A_4472, B_4473]: (r2_hidden('#skF_2'(A_4472, B_4473, A_4472), B_4473) | k4_xboole_0(A_4472, B_4473)=A_4472)), inference(resolution, [status(thm)], [c_221819, c_233790])).
% 53.88/42.85  tff(c_194222, plain, (![A_3460, B_3461, C_3462]: (r2_hidden('#skF_1'(A_3460, B_3461, C_3462), A_3460) | r2_hidden('#skF_2'(A_3460, B_3461, C_3462), C_3462) | k4_xboole_0(A_3460, B_3461)=C_3462)), inference(cnfTransformation, [status(thm)], [f_37])).
% 53.88/42.85  tff(c_194282, plain, (![A_3460, B_3461]: (r2_hidden('#skF_2'(A_3460, B_3461, A_3460), A_3460) | k4_xboole_0(A_3460, B_3461)=A_3460)), inference(resolution, [status(thm)], [c_194222, c_16])).
% 53.88/42.85  tff(c_194707, plain, (![A_3476, B_3477, C_3478]: (~r2_hidden('#skF_1'(A_3476, B_3477, C_3478), C_3478) | r2_hidden('#skF_2'(A_3476, B_3477, C_3478), B_3477) | ~r2_hidden('#skF_2'(A_3476, B_3477, C_3478), A_3476) | k4_xboole_0(A_3476, B_3477)=C_3478)), inference(cnfTransformation, [status(thm)], [f_37])).
% 53.88/42.85  tff(c_203780, plain, (![A_3650, B_3651]: (r2_hidden('#skF_2'(A_3650, B_3651, A_3650), B_3651) | ~r2_hidden('#skF_2'(A_3650, B_3651, A_3650), A_3650) | k4_xboole_0(A_3650, B_3651)=A_3650)), inference(resolution, [status(thm)], [c_14, c_194707])).
% 53.88/42.85  tff(c_218703, plain, (![A_3926, B_3927]: (r2_hidden('#skF_2'(A_3926, B_3927, A_3926), B_3927) | k4_xboole_0(A_3926, B_3927)=A_3926)), inference(resolution, [status(thm)], [c_194282, c_203780])).
% 53.88/42.85  tff(c_111680, plain, (![B_2139, A_2140]: (r1_xboole_0(B_2139, A_2140) | k3_xboole_0(A_2140, B_2139)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_97, c_26])).
% 53.88/42.85  tff(c_111689, plain, (k3_xboole_0('#skF_6', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_111680, c_111675])).
% 53.88/42.85  tff(c_167052, plain, (![A_2974, B_2975, C_2976]: (~r2_hidden('#skF_1'(A_2974, B_2975, C_2976), C_2976) | r2_hidden('#skF_2'(A_2974, B_2975, C_2976), C_2976) | k4_xboole_0(A_2974, B_2975)=C_2976)), inference(cnfTransformation, [status(thm)], [f_37])).
% 53.88/42.85  tff(c_167061, plain, (![A_3, B_4]: (r2_hidden('#skF_2'(A_3, B_4, A_3), A_3) | k4_xboole_0(A_3, B_4)=A_3)), inference(resolution, [status(thm)], [c_20, c_167052])).
% 53.88/42.85  tff(c_167240, plain, (![A_2992, B_2993, C_2994]: (r2_hidden('#skF_1'(A_2992, B_2993, C_2994), A_2992) | r2_hidden('#skF_2'(A_2992, B_2993, C_2994), B_2993) | ~r2_hidden('#skF_2'(A_2992, B_2993, C_2994), A_2992) | k4_xboole_0(A_2992, B_2993)=C_2994)), inference(cnfTransformation, [status(thm)], [f_37])).
% 53.88/42.85  tff(c_176621, plain, (![A_3164, B_3165]: (r2_hidden('#skF_2'(A_3164, B_3165, A_3164), B_3165) | ~r2_hidden('#skF_2'(A_3164, B_3165, A_3164), A_3164) | k4_xboole_0(A_3164, B_3165)=A_3164)), inference(resolution, [status(thm)], [c_167240, c_10])).
% 53.88/42.85  tff(c_190775, plain, (![A_3391, B_3392]: (r2_hidden('#skF_2'(A_3391, B_3392, A_3391), B_3392) | k4_xboole_0(A_3391, B_3392)=A_3391)), inference(resolution, [status(thm)], [c_167061, c_176621])).
% 53.88/42.85  tff(c_111694, plain, (r1_xboole_0('#skF_7', '#skF_9')), inference(splitLeft, [status(thm)], [c_52])).
% 53.88/42.85  tff(c_111700, plain, (k3_xboole_0('#skF_7', '#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_111694, c_22])).
% 53.88/42.85  tff(c_112675, plain, (![A_2208, B_2209, C_2210]: (r2_hidden('#skF_1'(A_2208, B_2209, C_2210), A_2208) | r2_hidden('#skF_2'(A_2208, B_2209, C_2210), C_2210) | k4_xboole_0(A_2208, B_2209)=C_2210)), inference(cnfTransformation, [status(thm)], [f_37])).
% 53.88/42.85  tff(c_112733, plain, (![A_2208, B_2209]: (r2_hidden('#skF_2'(A_2208, B_2209, A_2208), A_2208) | k4_xboole_0(A_2208, B_2209)=A_2208)), inference(resolution, [status(thm)], [c_112675, c_16])).
% 53.88/42.85  tff(c_113273, plain, (![A_2232, B_2233, C_2234]: (r2_hidden('#skF_1'(A_2232, B_2233, C_2234), A_2232) | r2_hidden('#skF_2'(A_2232, B_2233, C_2234), B_2233) | ~r2_hidden('#skF_2'(A_2232, B_2233, C_2234), A_2232) | k4_xboole_0(A_2232, B_2233)=C_2234)), inference(cnfTransformation, [status(thm)], [f_37])).
% 53.88/42.85  tff(c_122915, plain, (![A_2411, B_2412]: (r2_hidden('#skF_2'(A_2411, B_2412, A_2411), B_2412) | ~r2_hidden('#skF_2'(A_2411, B_2412, A_2411), A_2411) | k4_xboole_0(A_2411, B_2412)=A_2411)), inference(resolution, [status(thm)], [c_113273, c_10])).
% 53.88/42.85  tff(c_139087, plain, (![A_2678, B_2679]: (r2_hidden('#skF_2'(A_2678, B_2679, A_2678), B_2679) | k4_xboole_0(A_2678, B_2679)=A_2678)), inference(resolution, [status(thm)], [c_112733, c_122915])).
% 53.88/42.85  tff(c_114103, plain, (![A_2261, B_2262]: (r2_hidden('#skF_2'(A_2261, B_2262, A_2261), A_2261) | k4_xboole_0(A_2261, B_2262)=A_2261)), inference(resolution, [status(thm)], [c_112675, c_16])).
% 53.88/42.85  tff(c_111741, plain, (r1_xboole_0('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_51])).
% 53.88/42.85  tff(c_111858, plain, (![A_2158, B_2159, C_2160]: (~r1_xboole_0(A_2158, B_2159) | ~r2_hidden(C_2160, B_2159) | ~r2_hidden(C_2160, A_2158))), inference(cnfTransformation, [status(thm)], [f_63])).
% 53.88/42.85  tff(c_111876, plain, (![C_2160]: (~r2_hidden(C_2160, '#skF_8') | ~r2_hidden(C_2160, '#skF_7'))), inference(resolution, [status(thm)], [c_111741, c_111858])).
% 53.88/42.85  tff(c_114153, plain, (![B_2262]: (~r2_hidden('#skF_2'('#skF_7', B_2262, '#skF_7'), '#skF_8') | k4_xboole_0('#skF_7', B_2262)='#skF_7')), inference(resolution, [status(thm)], [c_114103, c_111876])).
% 53.88/42.85  tff(c_139192, plain, (k4_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_139087, c_114153])).
% 53.88/42.85  tff(c_38, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k4_xboole_0(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_69])).
% 53.88/42.85  tff(c_111949, plain, (![A_2167, B_2168, C_2169]: (k4_xboole_0(k4_xboole_0(A_2167, B_2168), C_2169)=k4_xboole_0(A_2167, k2_xboole_0(B_2168, C_2169)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 53.88/42.85  tff(c_111968, plain, (![A_2167, B_2168, C_2169]: (k4_xboole_0(k4_xboole_0(A_2167, B_2168), k4_xboole_0(A_2167, k2_xboole_0(B_2168, C_2169)))=k3_xboole_0(k4_xboole_0(A_2167, B_2168), C_2169))), inference(superposition, [status(thm), theory('equality')], [c_111949, c_38])).
% 53.88/42.85  tff(c_139957, plain, (![C_2169]: (k4_xboole_0('#skF_7', k4_xboole_0('#skF_7', k2_xboole_0('#skF_8', C_2169)))=k3_xboole_0(k4_xboole_0('#skF_7', '#skF_8'), C_2169))), inference(superposition, [status(thm), theory('equality')], [c_139192, c_111968])).
% 53.88/42.85  tff(c_140084, plain, (![C_2169]: (k3_xboole_0('#skF_7', k2_xboole_0('#skF_8', C_2169))=k3_xboole_0('#skF_7', C_2169))), inference(demodulation, [status(thm), theory('equality')], [c_139192, c_38, c_139957])).
% 53.88/42.85  tff(c_111838, plain, (~r1_xboole_0('#skF_7', k2_xboole_0('#skF_8', '#skF_9'))), inference(splitLeft, [status(thm)], [c_53])).
% 53.88/42.85  tff(c_111846, plain, (k3_xboole_0('#skF_7', k2_xboole_0('#skF_8', '#skF_9'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_111838])).
% 53.88/42.85  tff(c_166043, plain, (k3_xboole_0('#skF_7', '#skF_9')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_140084, c_111846])).
% 53.88/42.85  tff(c_166046, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_111700, c_166043])).
% 53.88/42.85  tff(c_166047, plain, (r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitRight, [status(thm)], [c_53])).
% 53.88/42.85  tff(c_166093, plain, (![A_2925, B_2926, C_2927]: (~r1_xboole_0(A_2925, B_2926) | ~r2_hidden(C_2927, B_2926) | ~r2_hidden(C_2927, A_2925))), inference(cnfTransformation, [status(thm)], [f_63])).
% 53.88/42.85  tff(c_166121, plain, (![C_2927]: (~r2_hidden(C_2927, k2_xboole_0('#skF_6', '#skF_5')) | ~r2_hidden(C_2927, '#skF_4'))), inference(resolution, [status(thm)], [c_166047, c_166093])).
% 53.88/42.85  tff(c_193030, plain, (![A_3404]: (~r2_hidden('#skF_2'(A_3404, k2_xboole_0('#skF_6', '#skF_5'), A_3404), '#skF_4') | k4_xboole_0(A_3404, k2_xboole_0('#skF_6', '#skF_5'))=A_3404)), inference(resolution, [status(thm)], [c_190775, c_166121])).
% 53.88/42.85  tff(c_193039, plain, (k4_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))='#skF_4'), inference(resolution, [status(thm)], [c_167061, c_193030])).
% 53.88/42.85  tff(c_111780, plain, (![A_2151, B_2152]: (r2_hidden('#skF_3'(A_2151, B_2152), B_2152) | r1_xboole_0(A_2151, B_2152))), inference(cnfTransformation, [status(thm)], [f_63])).
% 53.88/42.85  tff(c_171089, plain, (![A_3075, A_3076, B_3077]: (~r2_hidden('#skF_3'(A_3075, k4_xboole_0(A_3076, B_3077)), B_3077) | r1_xboole_0(A_3075, k4_xboole_0(A_3076, B_3077)))), inference(resolution, [status(thm)], [c_111780, c_6])).
% 53.88/42.85  tff(c_171186, plain, (![A_3078, A_3079]: (r1_xboole_0(A_3078, k4_xboole_0(A_3079, A_3078)))), inference(resolution, [status(thm)], [c_32, c_171089])).
% 53.88/42.85  tff(c_184234, plain, (![C_3284, A_3285, B_3286]: (r1_xboole_0(C_3284, k4_xboole_0(A_3285, k2_xboole_0(B_3286, C_3284))))), inference(superposition, [status(thm), theory('equality')], [c_36, c_171186])).
% 53.88/42.85  tff(c_184306, plain, (![B_2, A_3285, A_1]: (r1_xboole_0(B_2, k4_xboole_0(A_3285, k2_xboole_0(B_2, A_1))))), inference(superposition, [status(thm), theory('equality')], [c_2, c_184234])).
% 53.88/42.85  tff(c_193058, plain, (r1_xboole_0('#skF_6', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_193039, c_184306])).
% 53.88/42.85  tff(c_193318, plain, (k3_xboole_0('#skF_6', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_193058, c_22])).
% 53.88/42.85  tff(c_193325, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111689, c_193318])).
% 53.88/42.85  tff(c_193326, plain, (r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitRight, [status(thm)], [c_51])).
% 53.88/42.85  tff(c_193433, plain, (![A_3413, B_3414, C_3415]: (~r1_xboole_0(A_3413, B_3414) | ~r2_hidden(C_3415, B_3414) | ~r2_hidden(C_3415, A_3413))), inference(cnfTransformation, [status(thm)], [f_63])).
% 53.88/42.85  tff(c_193451, plain, (![C_3415]: (~r2_hidden(C_3415, k2_xboole_0('#skF_6', '#skF_5')) | ~r2_hidden(C_3415, '#skF_4'))), inference(resolution, [status(thm)], [c_193326, c_193433])).
% 53.88/42.85  tff(c_220243, plain, (![A_3933]: (~r2_hidden('#skF_2'(A_3933, k2_xboole_0('#skF_6', '#skF_5'), A_3933), '#skF_4') | k4_xboole_0(A_3933, k2_xboole_0('#skF_6', '#skF_5'))=A_3933)), inference(resolution, [status(thm)], [c_218703, c_193451])).
% 53.88/42.85  tff(c_220252, plain, (k4_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))='#skF_4'), inference(resolution, [status(thm)], [c_194282, c_220243])).
% 53.88/42.85  tff(c_193375, plain, (![A_3407, B_3408]: (r2_hidden('#skF_3'(A_3407, B_3408), B_3408) | r1_xboole_0(A_3407, B_3408))), inference(cnfTransformation, [status(thm)], [f_63])).
% 53.88/42.85  tff(c_197698, plain, (![A_3553, A_3554, B_3555]: (~r2_hidden('#skF_3'(A_3553, k4_xboole_0(A_3554, B_3555)), B_3555) | r1_xboole_0(A_3553, k4_xboole_0(A_3554, B_3555)))), inference(resolution, [status(thm)], [c_193375, c_6])).
% 53.88/42.85  tff(c_197791, plain, (![A_3556, A_3557]: (r1_xboole_0(A_3556, k4_xboole_0(A_3557, A_3556)))), inference(resolution, [status(thm)], [c_32, c_197698])).
% 53.88/42.85  tff(c_205761, plain, (![C_3686, A_3687, B_3688]: (r1_xboole_0(C_3686, k4_xboole_0(A_3687, k2_xboole_0(B_3688, C_3686))))), inference(superposition, [status(thm), theory('equality')], [c_36, c_197791])).
% 53.88/42.85  tff(c_211531, plain, (![A_3783, B_3784, C_3785]: (r1_xboole_0(k4_xboole_0(A_3783, k2_xboole_0(B_3784, C_3785)), C_3785))), inference(resolution, [status(thm)], [c_205761, c_26])).
% 53.88/42.85  tff(c_211603, plain, (![A_3783, B_2, A_1]: (r1_xboole_0(k4_xboole_0(A_3783, k2_xboole_0(B_2, A_1)), B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_211531])).
% 53.88/42.85  tff(c_220630, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_220252, c_211603])).
% 53.88/42.85  tff(c_220840, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111675, c_220630])).
% 53.88/42.85  tff(c_220841, plain, (r1_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(splitRight, [status(thm)], [c_52])).
% 53.88/42.85  tff(c_220976, plain, (![A_3955, B_3956, C_3957]: (~r1_xboole_0(A_3955, B_3956) | ~r2_hidden(C_3957, B_3956) | ~r2_hidden(C_3957, A_3955))), inference(cnfTransformation, [status(thm)], [f_63])).
% 53.88/42.85  tff(c_220990, plain, (![C_3957]: (~r2_hidden(C_3957, k2_xboole_0('#skF_6', '#skF_5')) | ~r2_hidden(C_3957, '#skF_4'))), inference(resolution, [status(thm)], [c_220841, c_220976])).
% 53.88/42.85  tff(c_248033, plain, (![A_4475]: (~r2_hidden('#skF_2'(A_4475, k2_xboole_0('#skF_6', '#skF_5'), A_4475), '#skF_4') | k4_xboole_0(A_4475, k2_xboole_0('#skF_6', '#skF_5'))=A_4475)), inference(resolution, [status(thm)], [c_247177, c_220990])).
% 53.88/42.85  tff(c_248042, plain, (k4_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))='#skF_4'), inference(resolution, [status(thm)], [c_221819, c_248033])).
% 53.88/42.85  tff(c_220897, plain, (![A_3945, B_3946]: (r2_hidden('#skF_3'(A_3945, B_3946), A_3945) | r1_xboole_0(A_3945, B_3946))), inference(cnfTransformation, [status(thm)], [f_63])).
% 53.88/42.85  tff(c_226882, plain, (![A_4114, B_4115, B_4116]: (~r2_hidden('#skF_3'(k4_xboole_0(A_4114, B_4115), B_4116), B_4115) | r1_xboole_0(k4_xboole_0(A_4114, B_4115), B_4116))), inference(resolution, [status(thm)], [c_220897, c_6])).
% 53.88/42.85  tff(c_226981, plain, (![A_4117, B_4118]: (r1_xboole_0(k4_xboole_0(A_4117, B_4118), B_4118))), inference(resolution, [status(thm)], [c_30, c_226882])).
% 53.88/42.85  tff(c_227297, plain, (![A_4127, B_4128]: (k3_xboole_0(k4_xboole_0(A_4127, B_4128), B_4128)=k1_xboole_0)), inference(resolution, [status(thm)], [c_226981, c_22])).
% 53.88/42.85  tff(c_242741, plain, (![A_4424, B_4425, C_4426]: (k3_xboole_0(k4_xboole_0(A_4424, k2_xboole_0(B_4425, C_4426)), C_4426)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_36, c_227297])).
% 53.88/42.85  tff(c_242931, plain, (![A_4424, A_1, B_2]: (k3_xboole_0(k4_xboole_0(A_4424, k2_xboole_0(A_1, B_2)), A_1)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_242741])).
% 53.88/42.85  tff(c_248054, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_248042, c_242931])).
% 53.88/42.85  tff(c_248330, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111679, c_248054])).
% 53.88/42.85  tff(c_248332, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_111650])).
% 53.88/42.85  tff(c_50, plain, (~r1_xboole_0('#skF_4', '#skF_6') | ~r1_xboole_0('#skF_4', '#skF_5') | ~r1_xboole_0('#skF_7', k2_xboole_0('#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 53.88/42.85  tff(c_248415, plain, (~r1_xboole_0('#skF_7', k2_xboole_0('#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_111651, c_248332, c_50])).
% 53.88/42.85  tff(c_249317, plain, (![A_4544, B_4545, C_4546]: (r2_hidden('#skF_1'(A_4544, B_4545, C_4546), A_4544) | r2_hidden('#skF_2'(A_4544, B_4545, C_4546), C_4546) | k4_xboole_0(A_4544, B_4545)=C_4546)), inference(cnfTransformation, [status(thm)], [f_37])).
% 53.88/42.85  tff(c_249381, plain, (![A_4544, B_4545]: (r2_hidden('#skF_2'(A_4544, B_4545, A_4544), A_4544) | k4_xboole_0(A_4544, B_4545)=A_4544)), inference(resolution, [status(thm)], [c_249317, c_16])).
% 53.88/42.85  tff(c_249564, plain, (![A_4558, B_4559, C_4560]: (~r2_hidden('#skF_1'(A_4558, B_4559, C_4560), C_4560) | r2_hidden('#skF_2'(A_4558, B_4559, C_4560), B_4559) | ~r2_hidden('#skF_2'(A_4558, B_4559, C_4560), A_4558) | k4_xboole_0(A_4558, B_4559)=C_4560)), inference(cnfTransformation, [status(thm)], [f_37])).
% 53.88/42.85  tff(c_258800, plain, (![A_4746, B_4747]: (r2_hidden('#skF_2'(A_4746, B_4747, A_4746), B_4747) | ~r2_hidden('#skF_2'(A_4746, B_4747, A_4746), A_4746) | k4_xboole_0(A_4746, B_4747)=A_4746)), inference(resolution, [status(thm)], [c_14, c_249564])).
% 53.88/42.85  tff(c_277530, plain, (![A_5024, B_5025]: (r2_hidden('#skF_2'(A_5024, B_5025, A_5024), B_5025) | k4_xboole_0(A_5024, B_5025)=A_5024)), inference(resolution, [status(thm)], [c_249381, c_258800])).
% 53.88/42.85  tff(c_250845, plain, (![A_4600, B_4601]: (r2_hidden('#skF_2'(A_4600, B_4601, A_4600), A_4600) | k4_xboole_0(A_4600, B_4601)=A_4600)), inference(resolution, [status(thm)], [c_249317, c_16])).
% 53.88/42.85  tff(c_248347, plain, (r1_xboole_0('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_51])).
% 53.88/42.85  tff(c_248557, plain, (![A_4497, B_4498, C_4499]: (~r1_xboole_0(A_4497, B_4498) | ~r2_hidden(C_4499, B_4498) | ~r2_hidden(C_4499, A_4497))), inference(cnfTransformation, [status(thm)], [f_63])).
% 53.88/42.85  tff(c_248582, plain, (![C_4499]: (~r2_hidden(C_4499, '#skF_8') | ~r2_hidden(C_4499, '#skF_7'))), inference(resolution, [status(thm)], [c_248347, c_248557])).
% 53.88/42.85  tff(c_250890, plain, (![B_4601]: (~r2_hidden('#skF_2'('#skF_7', B_4601, '#skF_7'), '#skF_8') | k4_xboole_0('#skF_7', B_4601)='#skF_7')), inference(resolution, [status(thm)], [c_250845, c_248582])).
% 53.88/42.85  tff(c_277643, plain, (k4_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_277530, c_250890])).
% 53.88/42.85  tff(c_248331, plain, (r1_xboole_0('#skF_7', '#skF_9')), inference(splitRight, [status(thm)], [c_111650])).
% 53.88/42.85  tff(c_248584, plain, (![C_4499]: (~r2_hidden(C_4499, '#skF_9') | ~r2_hidden(C_4499, '#skF_7'))), inference(resolution, [status(thm)], [c_248331, c_248557])).
% 53.88/42.85  tff(c_250892, plain, (![B_4601]: (~r2_hidden('#skF_2'('#skF_7', B_4601, '#skF_7'), '#skF_9') | k4_xboole_0('#skF_7', B_4601)='#skF_7')), inference(resolution, [status(thm)], [c_250845, c_248584])).
% 53.88/42.85  tff(c_277646, plain, (k4_xboole_0('#skF_7', '#skF_9')='#skF_7'), inference(resolution, [status(thm)], [c_277530, c_250892])).
% 53.88/42.85  tff(c_317364, plain, (![C_5404]: (k4_xboole_0('#skF_7', k2_xboole_0('#skF_9', C_5404))=k4_xboole_0('#skF_7', C_5404))), inference(superposition, [status(thm), theory('equality')], [c_277646, c_36])).
% 53.88/42.85  tff(c_248444, plain, (![A_4485, B_4486]: (r2_hidden('#skF_3'(A_4485, B_4486), B_4486) | r1_xboole_0(A_4485, B_4486))), inference(cnfTransformation, [status(thm)], [f_63])).
% 53.88/42.85  tff(c_252554, plain, (![A_4639, A_4640, B_4641]: (~r2_hidden('#skF_3'(A_4639, k4_xboole_0(A_4640, B_4641)), B_4641) | r1_xboole_0(A_4639, k4_xboole_0(A_4640, B_4641)))), inference(resolution, [status(thm)], [c_248444, c_6])).
% 53.88/42.85  tff(c_252638, plain, (![A_4642, A_4643]: (r1_xboole_0(A_4642, k4_xboole_0(A_4643, A_4642)))), inference(resolution, [status(thm)], [c_32, c_252554])).
% 53.88/42.85  tff(c_252699, plain, (![A_4643, A_4642]: (r1_xboole_0(k4_xboole_0(A_4643, A_4642), A_4642))), inference(resolution, [status(thm)], [c_252638, c_26])).
% 53.88/42.85  tff(c_317901, plain, (![C_5405]: (r1_xboole_0(k4_xboole_0('#skF_7', C_5405), k2_xboole_0('#skF_9', C_5405)))), inference(superposition, [status(thm), theory('equality')], [c_317364, c_252699])).
% 53.88/42.85  tff(c_317958, plain, (r1_xboole_0('#skF_7', k2_xboole_0('#skF_9', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_277643, c_317901])).
% 53.88/42.85  tff(c_318029, plain, (r1_xboole_0('#skF_7', k2_xboole_0('#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_317958])).
% 53.88/42.85  tff(c_318031, plain, $false, inference(negUnitSimplification, [status(thm)], [c_248415, c_318029])).
% 53.88/42.85  tff(c_318033, plain, (~r1_xboole_0('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_51])).
% 53.88/42.85  tff(c_46, plain, (~r1_xboole_0('#skF_4', '#skF_6') | ~r1_xboole_0('#skF_4', '#skF_5') | r1_xboole_0('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_86])).
% 53.88/42.85  tff(c_318070, plain, (r1_xboole_0('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_111651, c_248332, c_46])).
% 53.88/42.85  tff(c_318071, plain, $false, inference(negUnitSimplification, [status(thm)], [c_318033, c_318070])).
% 53.88/42.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 53.88/42.85  
% 53.88/42.85  Inference rules
% 53.88/42.85  ----------------------
% 53.88/42.85  #Ref     : 0
% 53.88/42.85  #Sup     : 78329
% 53.88/42.85  #Fact    : 0
% 53.88/42.85  #Define  : 0
% 53.88/42.85  #Split   : 66
% 53.88/42.85  #Chain   : 0
% 53.88/42.85  #Close   : 0
% 53.88/42.85  
% 53.88/42.85  Ordering : KBO
% 53.88/42.85  
% 53.88/42.85  Simplification rules
% 53.88/42.85  ----------------------
% 53.88/42.85  #Subsume      : 10530
% 53.88/42.85  #Demod        : 81185
% 53.88/42.85  #Tautology    : 40081
% 53.88/42.85  #SimpNegUnit  : 350
% 53.88/42.85  #BackRed      : 358
% 53.88/42.85  
% 53.88/42.85  #Partial instantiations: 0
% 53.88/42.85  #Strategies tried      : 1
% 53.88/42.85  
% 53.88/42.85  Timing (in seconds)
% 53.88/42.85  ----------------------
% 53.88/42.85  Preprocessing        : 0.30
% 53.88/42.85  Parsing              : 0.16
% 53.88/42.85  CNF conversion       : 0.02
% 53.88/42.85  Main loop            : 41.74
% 53.88/42.85  Inferencing          : 5.24
% 53.88/42.85  Reduction            : 24.78
% 53.88/42.85  Demodulation         : 21.76
% 53.88/42.85  BG Simplification    : 0.61
% 53.88/42.85  Subsumption          : 9.19
% 53.88/42.85  Abstraction          : 0.94
% 53.88/42.85  MUC search           : 0.00
% 53.88/42.85  Cooper               : 0.00
% 53.88/42.85  Total                : 42.11
% 53.88/42.85  Index Insertion      : 0.00
% 53.88/42.85  Index Deletion       : 0.00
% 53.88/42.85  Index Matching       : 0.00
% 53.88/42.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
