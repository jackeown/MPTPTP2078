%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:26 EST 2020

% Result     : Theorem 17.96s
% Output     : CNFRefutation 18.13s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 788 expanded)
%              Number of leaves         :   43 ( 278 expanded)
%              Depth                    :   19
%              Number of atoms          :  180 (1560 expanded)
%              Number of equality atoms :   70 ( 715 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_124,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_85,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_60,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_103,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(c_88,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_90,plain,(
    '#skF_9' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_92,plain,(
    k2_xboole_0('#skF_8','#skF_9') = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_136,plain,(
    ! [A_80,B_81] : k3_xboole_0(A_80,k2_xboole_0(A_80,B_81)) = A_80 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_145,plain,(
    k3_xboole_0('#skF_8',k1_tarski('#skF_7')) = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_136])).

tff(c_598,plain,(
    ! [D_142,B_143,A_144] :
      ( r2_hidden(D_142,B_143)
      | ~ r2_hidden(D_142,k3_xboole_0(A_144,B_143)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_622,plain,(
    ! [D_145] :
      ( r2_hidden(D_145,k1_tarski('#skF_7'))
      | ~ r2_hidden(D_145,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_598])).

tff(c_48,plain,(
    ! [C_35,A_31] :
      ( C_35 = A_31
      | ~ r2_hidden(C_35,k1_tarski(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_662,plain,(
    ! [D_148] :
      ( D_148 = '#skF_7'
      | ~ r2_hidden(D_148,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_622,c_48])).

tff(c_667,plain,
    ( '#skF_1'('#skF_8') = '#skF_7'
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_4,c_662])).

tff(c_668,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_667])).

tff(c_86,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_32,plain,(
    ! [B_17] : r1_tarski(B_17,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_294,plain,(
    ! [A_104,C_105,B_106] :
      ( r1_tarski(A_104,k2_xboole_0(C_105,B_106))
      | ~ r1_tarski(A_104,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_307,plain,(
    ! [A_104] :
      ( r1_tarski(A_104,k1_tarski('#skF_7'))
      | ~ r1_tarski(A_104,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_294])).

tff(c_635,plain,(
    ! [B_146,A_147] :
      ( k1_tarski(B_146) = A_147
      | k1_xboole_0 = A_147
      | ~ r1_tarski(A_147,k1_tarski(B_146)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_930,plain,(
    ! [A_177] :
      ( k1_tarski('#skF_7') = A_177
      | k1_xboole_0 = A_177
      | ~ r1_tarski(A_177,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_307,c_635])).

tff(c_938,plain,
    ( k1_tarski('#skF_7') = '#skF_9'
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_32,c_930])).

tff(c_944,plain,(
    k1_tarski('#skF_7') = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_938])).

tff(c_352,plain,(
    ! [A_112,B_113,C_114] :
      ( ~ r1_xboole_0(A_112,B_113)
      | ~ r2_hidden(C_114,k3_xboole_0(A_112,B_113)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_378,plain,(
    ! [A_117,B_118] :
      ( ~ r1_xboole_0(A_117,B_118)
      | v1_xboole_0(k3_xboole_0(A_117,B_118)) ) ),
    inference(resolution,[status(thm)],[c_4,c_352])).

tff(c_390,plain,
    ( ~ r1_xboole_0('#skF_8',k1_tarski('#skF_7'))
    | v1_xboole_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_378])).

tff(c_395,plain,(
    ~ r1_xboole_0('#skF_8',k1_tarski('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_390])).

tff(c_950,plain,(
    ~ r1_xboole_0('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_944,c_395])).

tff(c_952,plain,(
    k3_xboole_0('#skF_8','#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_944,c_145])).

tff(c_1047,plain,(
    ! [A_178,B_179] :
      ( r2_hidden('#skF_4'(A_178,B_179),k3_xboole_0(A_178,B_179))
      | r1_xboole_0(A_178,B_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1065,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_9'),'#skF_8')
    | r1_xboole_0('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_952,c_1047])).

tff(c_1083,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_950,c_1065])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1263,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_1083,c_2])).

tff(c_1269,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_668,c_1263])).

tff(c_1271,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_667])).

tff(c_1270,plain,(
    '#skF_1'('#skF_8') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_667])).

tff(c_1279,plain,
    ( v1_xboole_0('#skF_8')
    | r2_hidden('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1270,c_4])).

tff(c_1282,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_1271,c_1279])).

tff(c_1633,plain,(
    ! [A_213] :
      ( k1_tarski('#skF_7') = A_213
      | k1_xboole_0 = A_213
      | ~ r1_tarski(A_213,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_307,c_635])).

tff(c_1641,plain,
    ( k1_tarski('#skF_7') = '#skF_9'
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_32,c_1633])).

tff(c_1647,plain,(
    k1_tarski('#skF_7') = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1641])).

tff(c_76,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(k1_tarski(A_64),B_65)
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1989,plain,(
    ! [B_225] :
      ( r1_tarski('#skF_9',B_225)
      | ~ r2_hidden('#skF_7',B_225) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1647,c_76])).

tff(c_2019,plain,(
    r1_tarski('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_1282,c_1989])).

tff(c_40,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = A_25
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2030,plain,(
    k3_xboole_0('#skF_9','#skF_8') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_2019,c_40])).

tff(c_310,plain,(
    ! [A_107] :
      ( r1_tarski(A_107,k1_tarski('#skF_7'))
      | ~ r1_tarski(A_107,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_294])).

tff(c_74,plain,(
    ! [A_64,B_65] :
      ( r2_hidden(A_64,B_65)
      | ~ r1_tarski(k1_tarski(A_64),B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1347,plain,(
    ! [A_198] :
      ( r2_hidden(A_198,k1_tarski('#skF_7'))
      | ~ r1_tarski(k1_tarski(A_198),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_310,c_74])).

tff(c_1360,plain,(
    ! [A_199] :
      ( A_199 = '#skF_7'
      | ~ r1_tarski(k1_tarski(A_199),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1347,c_48])).

tff(c_1366,plain,(
    ! [A_200] :
      ( A_200 = '#skF_7'
      | ~ r2_hidden(A_200,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_76,c_1360])).

tff(c_1371,plain,
    ( '#skF_1'('#skF_9') = '#skF_7'
    | v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_4,c_1366])).

tff(c_1372,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1371])).

tff(c_1448,plain,(
    ! [A_207] :
      ( k1_tarski('#skF_7') = A_207
      | k1_xboole_0 = A_207
      | ~ r1_tarski(A_207,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_307,c_635])).

tff(c_1456,plain,
    ( k1_tarski('#skF_7') = '#skF_9'
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_32,c_1448])).

tff(c_1462,plain,(
    k1_tarski('#skF_7') = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1456])).

tff(c_50,plain,(
    ! [C_35] : r2_hidden(C_35,k1_tarski(C_35)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_107,plain,(
    ! [B_74,A_75] :
      ( ~ r2_hidden(B_74,A_75)
      | ~ v1_xboole_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_111,plain,(
    ! [C_35] : ~ v1_xboole_0(k1_tarski(C_35)) ),
    inference(resolution,[status(thm)],[c_50,c_107])).

tff(c_1517,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_1462,c_111])).

tff(c_1531,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1372,c_1517])).

tff(c_1533,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_1371])).

tff(c_1532,plain,(
    '#skF_1'('#skF_9') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1371])).

tff(c_1541,plain,
    ( v1_xboole_0('#skF_9')
    | r2_hidden('#skF_7','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_1532,c_4])).

tff(c_1544,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_1533,c_1541])).

tff(c_20,plain,(
    ! [A_5,B_6,C_7] :
      ( r2_hidden('#skF_2'(A_5,B_6,C_7),B_6)
      | r2_hidden('#skF_3'(A_5,B_6,C_7),C_7)
      | k3_xboole_0(A_5,B_6) = C_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3324,plain,(
    ! [A_304,B_305,C_306] :
      ( ~ r2_hidden('#skF_2'(A_304,B_305,C_306),C_306)
      | r2_hidden('#skF_3'(A_304,B_305,C_306),C_306)
      | k3_xboole_0(A_304,B_305) = C_306 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_7126,plain,(
    ! [A_480,B_481] :
      ( r2_hidden('#skF_3'(A_480,B_481,B_481),B_481)
      | k3_xboole_0(A_480,B_481) = B_481 ) ),
    inference(resolution,[status(thm)],[c_20,c_3324])).

tff(c_633,plain,(
    ! [D_145] :
      ( D_145 = '#skF_7'
      | ~ r2_hidden(D_145,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_622,c_48])).

tff(c_50502,plain,(
    ! [A_32779] :
      ( '#skF_3'(A_32779,'#skF_8','#skF_8') = '#skF_7'
      | k3_xboole_0(A_32779,'#skF_8') = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_7126,c_633])).

tff(c_50930,plain,
    ( '#skF_9' = '#skF_8'
    | '#skF_3'('#skF_9','#skF_8','#skF_8') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_50502,c_2030])).

tff(c_51084,plain,(
    '#skF_3'('#skF_9','#skF_8','#skF_8') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_50930])).

tff(c_16,plain,(
    ! [A_5,B_6,C_7] :
      ( r2_hidden('#skF_2'(A_5,B_6,C_7),A_5)
      | ~ r2_hidden('#skF_3'(A_5,B_6,C_7),B_6)
      | ~ r2_hidden('#skF_3'(A_5,B_6,C_7),A_5)
      | k3_xboole_0(A_5,B_6) = C_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_51114,plain,
    ( r2_hidden('#skF_2'('#skF_9','#skF_8','#skF_8'),'#skF_9')
    | ~ r2_hidden('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_3'('#skF_9','#skF_8','#skF_8'),'#skF_9')
    | k3_xboole_0('#skF_9','#skF_8') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_51084,c_16])).

tff(c_51128,plain,
    ( r2_hidden('#skF_2'('#skF_9','#skF_8','#skF_8'),'#skF_9')
    | '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2030,c_1544,c_51084,c_1282,c_51114])).

tff(c_51129,plain,(
    r2_hidden('#skF_2'('#skF_9','#skF_8','#skF_8'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_51128])).

tff(c_1365,plain,(
    ! [A_64] :
      ( A_64 = '#skF_7'
      | ~ r2_hidden(A_64,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_76,c_1360])).

tff(c_51173,plain,(
    '#skF_2'('#skF_9','#skF_8','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_51129,c_1365])).

tff(c_12,plain,(
    ! [A_5,B_6,C_7] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6,C_7),C_7)
      | ~ r2_hidden('#skF_3'(A_5,B_6,C_7),B_6)
      | ~ r2_hidden('#skF_3'(A_5,B_6,C_7),A_5)
      | k3_xboole_0(A_5,B_6) = C_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_51189,plain,
    ( ~ r2_hidden('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_3'('#skF_9','#skF_8','#skF_8'),'#skF_8')
    | ~ r2_hidden('#skF_3'('#skF_9','#skF_8','#skF_8'),'#skF_9')
    | k3_xboole_0('#skF_9','#skF_8') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_51173,c_12])).

tff(c_51209,plain,(
    '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2030,c_1544,c_51084,c_1282,c_51084,c_1282,c_51189])).

tff(c_51211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_51209])).

tff(c_51213,plain,(
    r1_xboole_0('#skF_8',k1_tarski('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_390])).

tff(c_44,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = A_29
      | ~ r1_xboole_0(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_51233,plain,(
    k4_xboole_0('#skF_8',k1_tarski('#skF_7')) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_51213,c_44])).

tff(c_117,plain,(
    ! [A_77,B_78] : k4_xboole_0(A_77,k2_xboole_0(A_77,B_78)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_124,plain,(
    k4_xboole_0('#skF_8',k1_tarski('#skF_7')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_117])).

tff(c_51262,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51233,c_124])).

tff(c_51264,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_51262])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:26:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.96/8.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.96/8.41  
% 17.96/8.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.96/8.42  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 17.96/8.42  
% 17.96/8.42  %Foreground sorts:
% 17.96/8.42  
% 17.96/8.42  
% 17.96/8.42  %Background operators:
% 17.96/8.42  
% 17.96/8.42  
% 17.96/8.42  %Foreground operators:
% 17.96/8.42  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 17.96/8.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.96/8.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.96/8.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 17.96/8.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 17.96/8.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 17.96/8.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.96/8.42  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 17.96/8.42  tff('#skF_7', type, '#skF_7': $i).
% 17.96/8.42  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 17.96/8.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.96/8.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 17.96/8.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 17.96/8.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 17.96/8.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 17.96/8.42  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 17.96/8.42  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 17.96/8.42  tff('#skF_9', type, '#skF_9': $i).
% 17.96/8.42  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 17.96/8.42  tff('#skF_8', type, '#skF_8': $i).
% 17.96/8.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.96/8.42  tff(k3_tarski, type, k3_tarski: $i > $i).
% 17.96/8.42  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 17.96/8.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.96/8.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 17.96/8.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 17.96/8.42  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 17.96/8.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 17.96/8.42  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 17.96/8.42  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 17.96/8.42  
% 18.13/8.44  tff(f_124, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 18.13/8.44  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 18.13/8.44  tff(f_68, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 18.13/8.44  tff(f_40, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 18.13/8.44  tff(f_85, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 18.13/8.44  tff(f_60, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 18.13/8.44  tff(f_66, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 18.13/8.44  tff(f_109, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 18.13/8.44  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 18.13/8.44  tff(f_103, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 18.13/8.44  tff(f_72, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 18.13/8.44  tff(f_78, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 18.13/8.44  tff(f_74, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 18.13/8.44  tff(c_88, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_124])).
% 18.13/8.44  tff(c_90, plain, ('#skF_9'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_124])).
% 18.13/8.44  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 18.13/8.44  tff(c_92, plain, (k2_xboole_0('#skF_8', '#skF_9')=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_124])).
% 18.13/8.44  tff(c_136, plain, (![A_80, B_81]: (k3_xboole_0(A_80, k2_xboole_0(A_80, B_81))=A_80)), inference(cnfTransformation, [status(thm)], [f_68])).
% 18.13/8.44  tff(c_145, plain, (k3_xboole_0('#skF_8', k1_tarski('#skF_7'))='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_92, c_136])).
% 18.13/8.44  tff(c_598, plain, (![D_142, B_143, A_144]: (r2_hidden(D_142, B_143) | ~r2_hidden(D_142, k3_xboole_0(A_144, B_143)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 18.13/8.44  tff(c_622, plain, (![D_145]: (r2_hidden(D_145, k1_tarski('#skF_7')) | ~r2_hidden(D_145, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_145, c_598])).
% 18.13/8.44  tff(c_48, plain, (![C_35, A_31]: (C_35=A_31 | ~r2_hidden(C_35, k1_tarski(A_31)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 18.13/8.44  tff(c_662, plain, (![D_148]: (D_148='#skF_7' | ~r2_hidden(D_148, '#skF_8'))), inference(resolution, [status(thm)], [c_622, c_48])).
% 18.13/8.44  tff(c_667, plain, ('#skF_1'('#skF_8')='#skF_7' | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_4, c_662])).
% 18.13/8.44  tff(c_668, plain, (v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_667])).
% 18.13/8.44  tff(c_86, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_124])).
% 18.13/8.44  tff(c_32, plain, (![B_17]: (r1_tarski(B_17, B_17))), inference(cnfTransformation, [status(thm)], [f_60])).
% 18.13/8.44  tff(c_294, plain, (![A_104, C_105, B_106]: (r1_tarski(A_104, k2_xboole_0(C_105, B_106)) | ~r1_tarski(A_104, B_106))), inference(cnfTransformation, [status(thm)], [f_66])).
% 18.13/8.44  tff(c_307, plain, (![A_104]: (r1_tarski(A_104, k1_tarski('#skF_7')) | ~r1_tarski(A_104, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_92, c_294])).
% 18.13/8.44  tff(c_635, plain, (![B_146, A_147]: (k1_tarski(B_146)=A_147 | k1_xboole_0=A_147 | ~r1_tarski(A_147, k1_tarski(B_146)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 18.13/8.44  tff(c_930, plain, (![A_177]: (k1_tarski('#skF_7')=A_177 | k1_xboole_0=A_177 | ~r1_tarski(A_177, '#skF_9'))), inference(resolution, [status(thm)], [c_307, c_635])).
% 18.13/8.44  tff(c_938, plain, (k1_tarski('#skF_7')='#skF_9' | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_32, c_930])).
% 18.13/8.44  tff(c_944, plain, (k1_tarski('#skF_7')='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_86, c_938])).
% 18.13/8.44  tff(c_352, plain, (![A_112, B_113, C_114]: (~r1_xboole_0(A_112, B_113) | ~r2_hidden(C_114, k3_xboole_0(A_112, B_113)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 18.13/8.44  tff(c_378, plain, (![A_117, B_118]: (~r1_xboole_0(A_117, B_118) | v1_xboole_0(k3_xboole_0(A_117, B_118)))), inference(resolution, [status(thm)], [c_4, c_352])).
% 18.13/8.44  tff(c_390, plain, (~r1_xboole_0('#skF_8', k1_tarski('#skF_7')) | v1_xboole_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_145, c_378])).
% 18.13/8.44  tff(c_395, plain, (~r1_xboole_0('#skF_8', k1_tarski('#skF_7'))), inference(splitLeft, [status(thm)], [c_390])).
% 18.13/8.44  tff(c_950, plain, (~r1_xboole_0('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_944, c_395])).
% 18.13/8.44  tff(c_952, plain, (k3_xboole_0('#skF_8', '#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_944, c_145])).
% 18.13/8.44  tff(c_1047, plain, (![A_178, B_179]: (r2_hidden('#skF_4'(A_178, B_179), k3_xboole_0(A_178, B_179)) | r1_xboole_0(A_178, B_179))), inference(cnfTransformation, [status(thm)], [f_54])).
% 18.13/8.44  tff(c_1065, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_9'), '#skF_8') | r1_xboole_0('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_952, c_1047])).
% 18.13/8.44  tff(c_1083, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_950, c_1065])).
% 18.13/8.44  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 18.13/8.44  tff(c_1263, plain, (~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_1083, c_2])).
% 18.13/8.44  tff(c_1269, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_668, c_1263])).
% 18.13/8.44  tff(c_1271, plain, (~v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_667])).
% 18.13/8.44  tff(c_1270, plain, ('#skF_1'('#skF_8')='#skF_7'), inference(splitRight, [status(thm)], [c_667])).
% 18.13/8.44  tff(c_1279, plain, (v1_xboole_0('#skF_8') | r2_hidden('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1270, c_4])).
% 18.13/8.44  tff(c_1282, plain, (r2_hidden('#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_1271, c_1279])).
% 18.13/8.44  tff(c_1633, plain, (![A_213]: (k1_tarski('#skF_7')=A_213 | k1_xboole_0=A_213 | ~r1_tarski(A_213, '#skF_9'))), inference(resolution, [status(thm)], [c_307, c_635])).
% 18.13/8.44  tff(c_1641, plain, (k1_tarski('#skF_7')='#skF_9' | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_32, c_1633])).
% 18.13/8.44  tff(c_1647, plain, (k1_tarski('#skF_7')='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_86, c_1641])).
% 18.13/8.44  tff(c_76, plain, (![A_64, B_65]: (r1_tarski(k1_tarski(A_64), B_65) | ~r2_hidden(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_103])).
% 18.13/8.44  tff(c_1989, plain, (![B_225]: (r1_tarski('#skF_9', B_225) | ~r2_hidden('#skF_7', B_225))), inference(superposition, [status(thm), theory('equality')], [c_1647, c_76])).
% 18.13/8.44  tff(c_2019, plain, (r1_tarski('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_1282, c_1989])).
% 18.13/8.44  tff(c_40, plain, (![A_25, B_26]: (k3_xboole_0(A_25, B_26)=A_25 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_72])).
% 18.13/8.44  tff(c_2030, plain, (k3_xboole_0('#skF_9', '#skF_8')='#skF_9'), inference(resolution, [status(thm)], [c_2019, c_40])).
% 18.13/8.44  tff(c_310, plain, (![A_107]: (r1_tarski(A_107, k1_tarski('#skF_7')) | ~r1_tarski(A_107, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_92, c_294])).
% 18.13/8.44  tff(c_74, plain, (![A_64, B_65]: (r2_hidden(A_64, B_65) | ~r1_tarski(k1_tarski(A_64), B_65))), inference(cnfTransformation, [status(thm)], [f_103])).
% 18.13/8.44  tff(c_1347, plain, (![A_198]: (r2_hidden(A_198, k1_tarski('#skF_7')) | ~r1_tarski(k1_tarski(A_198), '#skF_9'))), inference(resolution, [status(thm)], [c_310, c_74])).
% 18.13/8.44  tff(c_1360, plain, (![A_199]: (A_199='#skF_7' | ~r1_tarski(k1_tarski(A_199), '#skF_9'))), inference(resolution, [status(thm)], [c_1347, c_48])).
% 18.13/8.44  tff(c_1366, plain, (![A_200]: (A_200='#skF_7' | ~r2_hidden(A_200, '#skF_9'))), inference(resolution, [status(thm)], [c_76, c_1360])).
% 18.13/8.44  tff(c_1371, plain, ('#skF_1'('#skF_9')='#skF_7' | v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_4, c_1366])).
% 18.13/8.44  tff(c_1372, plain, (v1_xboole_0('#skF_9')), inference(splitLeft, [status(thm)], [c_1371])).
% 18.13/8.44  tff(c_1448, plain, (![A_207]: (k1_tarski('#skF_7')=A_207 | k1_xboole_0=A_207 | ~r1_tarski(A_207, '#skF_9'))), inference(resolution, [status(thm)], [c_307, c_635])).
% 18.13/8.44  tff(c_1456, plain, (k1_tarski('#skF_7')='#skF_9' | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_32, c_1448])).
% 18.13/8.44  tff(c_1462, plain, (k1_tarski('#skF_7')='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_86, c_1456])).
% 18.13/8.44  tff(c_50, plain, (![C_35]: (r2_hidden(C_35, k1_tarski(C_35)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 18.13/8.44  tff(c_107, plain, (![B_74, A_75]: (~r2_hidden(B_74, A_75) | ~v1_xboole_0(A_75))), inference(cnfTransformation, [status(thm)], [f_31])).
% 18.13/8.44  tff(c_111, plain, (![C_35]: (~v1_xboole_0(k1_tarski(C_35)))), inference(resolution, [status(thm)], [c_50, c_107])).
% 18.13/8.44  tff(c_1517, plain, (~v1_xboole_0('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_1462, c_111])).
% 18.13/8.44  tff(c_1531, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1372, c_1517])).
% 18.13/8.44  tff(c_1533, plain, (~v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_1371])).
% 18.13/8.44  tff(c_1532, plain, ('#skF_1'('#skF_9')='#skF_7'), inference(splitRight, [status(thm)], [c_1371])).
% 18.13/8.44  tff(c_1541, plain, (v1_xboole_0('#skF_9') | r2_hidden('#skF_7', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_1532, c_4])).
% 18.13/8.44  tff(c_1544, plain, (r2_hidden('#skF_7', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_1533, c_1541])).
% 18.13/8.44  tff(c_20, plain, (![A_5, B_6, C_7]: (r2_hidden('#skF_2'(A_5, B_6, C_7), B_6) | r2_hidden('#skF_3'(A_5, B_6, C_7), C_7) | k3_xboole_0(A_5, B_6)=C_7)), inference(cnfTransformation, [status(thm)], [f_40])).
% 18.13/8.44  tff(c_3324, plain, (![A_304, B_305, C_306]: (~r2_hidden('#skF_2'(A_304, B_305, C_306), C_306) | r2_hidden('#skF_3'(A_304, B_305, C_306), C_306) | k3_xboole_0(A_304, B_305)=C_306)), inference(cnfTransformation, [status(thm)], [f_40])).
% 18.13/8.44  tff(c_7126, plain, (![A_480, B_481]: (r2_hidden('#skF_3'(A_480, B_481, B_481), B_481) | k3_xboole_0(A_480, B_481)=B_481)), inference(resolution, [status(thm)], [c_20, c_3324])).
% 18.13/8.44  tff(c_633, plain, (![D_145]: (D_145='#skF_7' | ~r2_hidden(D_145, '#skF_8'))), inference(resolution, [status(thm)], [c_622, c_48])).
% 18.13/8.44  tff(c_50502, plain, (![A_32779]: ('#skF_3'(A_32779, '#skF_8', '#skF_8')='#skF_7' | k3_xboole_0(A_32779, '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_7126, c_633])).
% 18.13/8.44  tff(c_50930, plain, ('#skF_9'='#skF_8' | '#skF_3'('#skF_9', '#skF_8', '#skF_8')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_50502, c_2030])).
% 18.13/8.44  tff(c_51084, plain, ('#skF_3'('#skF_9', '#skF_8', '#skF_8')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_90, c_50930])).
% 18.13/8.44  tff(c_16, plain, (![A_5, B_6, C_7]: (r2_hidden('#skF_2'(A_5, B_6, C_7), A_5) | ~r2_hidden('#skF_3'(A_5, B_6, C_7), B_6) | ~r2_hidden('#skF_3'(A_5, B_6, C_7), A_5) | k3_xboole_0(A_5, B_6)=C_7)), inference(cnfTransformation, [status(thm)], [f_40])).
% 18.13/8.44  tff(c_51114, plain, (r2_hidden('#skF_2'('#skF_9', '#skF_8', '#skF_8'), '#skF_9') | ~r2_hidden('#skF_7', '#skF_8') | ~r2_hidden('#skF_3'('#skF_9', '#skF_8', '#skF_8'), '#skF_9') | k3_xboole_0('#skF_9', '#skF_8')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_51084, c_16])).
% 18.13/8.44  tff(c_51128, plain, (r2_hidden('#skF_2'('#skF_9', '#skF_8', '#skF_8'), '#skF_9') | '#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2030, c_1544, c_51084, c_1282, c_51114])).
% 18.13/8.44  tff(c_51129, plain, (r2_hidden('#skF_2'('#skF_9', '#skF_8', '#skF_8'), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_90, c_51128])).
% 18.13/8.44  tff(c_1365, plain, (![A_64]: (A_64='#skF_7' | ~r2_hidden(A_64, '#skF_9'))), inference(resolution, [status(thm)], [c_76, c_1360])).
% 18.13/8.44  tff(c_51173, plain, ('#skF_2'('#skF_9', '#skF_8', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_51129, c_1365])).
% 18.13/8.44  tff(c_12, plain, (![A_5, B_6, C_7]: (~r2_hidden('#skF_2'(A_5, B_6, C_7), C_7) | ~r2_hidden('#skF_3'(A_5, B_6, C_7), B_6) | ~r2_hidden('#skF_3'(A_5, B_6, C_7), A_5) | k3_xboole_0(A_5, B_6)=C_7)), inference(cnfTransformation, [status(thm)], [f_40])).
% 18.13/8.44  tff(c_51189, plain, (~r2_hidden('#skF_7', '#skF_8') | ~r2_hidden('#skF_3'('#skF_9', '#skF_8', '#skF_8'), '#skF_8') | ~r2_hidden('#skF_3'('#skF_9', '#skF_8', '#skF_8'), '#skF_9') | k3_xboole_0('#skF_9', '#skF_8')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_51173, c_12])).
% 18.13/8.44  tff(c_51209, plain, ('#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2030, c_1544, c_51084, c_1282, c_51084, c_1282, c_51189])).
% 18.13/8.44  tff(c_51211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_51209])).
% 18.13/8.44  tff(c_51213, plain, (r1_xboole_0('#skF_8', k1_tarski('#skF_7'))), inference(splitRight, [status(thm)], [c_390])).
% 18.13/8.44  tff(c_44, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=A_29 | ~r1_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_78])).
% 18.13/8.44  tff(c_51233, plain, (k4_xboole_0('#skF_8', k1_tarski('#skF_7'))='#skF_8'), inference(resolution, [status(thm)], [c_51213, c_44])).
% 18.13/8.44  tff(c_117, plain, (![A_77, B_78]: (k4_xboole_0(A_77, k2_xboole_0(A_77, B_78))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_74])).
% 18.13/8.44  tff(c_124, plain, (k4_xboole_0('#skF_8', k1_tarski('#skF_7'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_92, c_117])).
% 18.13/8.44  tff(c_51262, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_51233, c_124])).
% 18.13/8.44  tff(c_51264, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_51262])).
% 18.13/8.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.13/8.44  
% 18.13/8.44  Inference rules
% 18.13/8.44  ----------------------
% 18.13/8.44  #Ref     : 5
% 18.13/8.44  #Sup     : 12080
% 18.13/8.44  #Fact    : 0
% 18.13/8.44  #Define  : 0
% 18.13/8.44  #Split   : 15
% 18.13/8.44  #Chain   : 0
% 18.13/8.44  #Close   : 0
% 18.13/8.44  
% 18.13/8.44  Ordering : KBO
% 18.13/8.44  
% 18.13/8.44  Simplification rules
% 18.13/8.44  ----------------------
% 18.13/8.44  #Subsume      : 4722
% 18.13/8.44  #Demod        : 4058
% 18.13/8.44  #Tautology    : 3092
% 18.13/8.44  #SimpNegUnit  : 764
% 18.13/8.44  #BackRed      : 45
% 18.13/8.44  
% 18.13/8.44  #Partial instantiations: 12489
% 18.13/8.44  #Strategies tried      : 1
% 18.13/8.44  
% 18.13/8.44  Timing (in seconds)
% 18.13/8.44  ----------------------
% 18.13/8.44  Preprocessing        : 0.37
% 18.13/8.44  Parsing              : 0.19
% 18.13/8.44  CNF conversion       : 0.03
% 18.13/8.44  Main loop            : 7.29
% 18.13/8.44  Inferencing          : 1.52
% 18.13/8.44  Reduction            : 2.78
% 18.13/8.44  Demodulation         : 2.03
% 18.13/8.44  BG Simplification    : 0.13
% 18.13/8.44  Subsumption          : 2.47
% 18.13/8.44  Abstraction          : 0.20
% 18.13/8.44  MUC search           : 0.00
% 18.13/8.44  Cooper               : 0.00
% 18.13/8.44  Total                : 7.70
% 18.13/8.44  Index Insertion      : 0.00
% 18.13/8.44  Index Deletion       : 0.00
% 18.13/8.44  Index Matching       : 0.00
% 18.13/8.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
