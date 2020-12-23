%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:20 EST 2020

% Result     : Theorem 4.68s
% Output     : CNFRefutation 4.88s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 394 expanded)
%              Number of leaves         :   42 ( 146 expanded)
%              Depth                    :   14
%              Number of atoms          :  179 ( 909 expanded)
%              Number of equality atoms :   95 ( 541 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_11 > #skF_6 > #skF_8 > #skF_4 > #skF_13 > #skF_5 > #skF_10 > #skF_2 > #skF_7 > #skF_3 > #skF_1 > #skF_9 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_124,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_68,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_89,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_76,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_103,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_82,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_106,plain,
    ( k1_tarski('#skF_11') != '#skF_13'
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_135,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_62,plain,(
    ! [A_24] :
      ( r2_hidden('#skF_8'(A_24),A_24)
      | k1_xboole_0 = A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_110,plain,(
    k2_xboole_0('#skF_12','#skF_13') = k1_tarski('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_516,plain,(
    ! [D_106,B_107,A_108] :
      ( ~ r2_hidden(D_106,B_107)
      | r2_hidden(D_106,k2_xboole_0(A_108,B_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_529,plain,(
    ! [D_109] :
      ( ~ r2_hidden(D_109,'#skF_13')
      | r2_hidden(D_109,k1_tarski('#skF_11')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_516])).

tff(c_76,plain,(
    ! [C_39,A_35] :
      ( C_39 = A_35
      | ~ r2_hidden(C_39,k1_tarski(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_534,plain,(
    ! [D_110] :
      ( D_110 = '#skF_11'
      | ~ r2_hidden(D_110,'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_529,c_76])).

tff(c_544,plain,
    ( '#skF_8'('#skF_13') = '#skF_11'
    | k1_xboole_0 = '#skF_13' ),
    inference(resolution,[status(thm)],[c_62,c_534])).

tff(c_545,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_544])).

tff(c_582,plain,(
    '#skF_13' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_545,c_135])).

tff(c_104,plain,
    ( k1_xboole_0 != '#skF_13'
    | k1_tarski('#skF_11') != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_120,plain,(
    k1_tarski('#skF_11') != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_137,plain,(
    ! [A_60,B_61] : k3_xboole_0(A_60,k2_xboole_0(A_60,B_61)) = A_60 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_146,plain,(
    k3_xboole_0('#skF_12',k1_tarski('#skF_11')) = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_137])).

tff(c_303,plain,(
    ! [D_84,B_85,A_86] :
      ( r2_hidden(D_84,B_85)
      | ~ r2_hidden(D_84,k3_xboole_0(A_86,B_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_312,plain,(
    ! [D_84] :
      ( r2_hidden(D_84,k1_tarski('#skF_11'))
      | ~ r2_hidden(D_84,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_303])).

tff(c_818,plain,(
    ! [A_131,B_132] :
      ( ~ r2_hidden('#skF_1'(A_131,B_132),B_132)
      | r1_tarski(A_131,B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_890,plain,(
    ! [A_136] :
      ( r1_tarski(A_136,k1_tarski('#skF_11'))
      | ~ r2_hidden('#skF_1'(A_136,k1_tarski('#skF_11')),'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_312,c_818])).

tff(c_895,plain,(
    r1_tarski('#skF_12',k1_tarski('#skF_11')) ),
    inference(resolution,[status(thm)],[c_6,c_890])).

tff(c_96,plain,(
    ! [B_51,A_50] :
      ( k1_tarski(B_51) = A_50
      | k1_xboole_0 = A_50
      | ~ r1_tarski(A_50,k1_tarski(B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_937,plain,(
    ! [B_139,A_140] :
      ( k1_tarski(B_139) = A_140
      | A_140 = '#skF_13'
      | ~ r1_tarski(A_140,k1_tarski(B_139)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_545,c_96])).

tff(c_940,plain,
    ( k1_tarski('#skF_11') = '#skF_12'
    | '#skF_13' = '#skF_12' ),
    inference(resolution,[status(thm)],[c_895,c_937])).

tff(c_959,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_582,c_120,c_940])).

tff(c_961,plain,(
    k1_xboole_0 != '#skF_13' ),
    inference(splitRight,[status(thm)],[c_544])).

tff(c_528,plain,(
    ! [D_106] :
      ( ~ r2_hidden(D_106,'#skF_13')
      | r2_hidden(D_106,k1_tarski('#skF_11')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_516])).

tff(c_1069,plain,(
    ! [A_150,B_151] :
      ( ~ r2_hidden('#skF_1'(A_150,B_151),B_151)
      | r1_tarski(A_150,B_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1275,plain,(
    ! [A_162] :
      ( r1_tarski(A_162,k1_tarski('#skF_11'))
      | ~ r2_hidden('#skF_1'(A_162,k1_tarski('#skF_11')),'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_528,c_1069])).

tff(c_1280,plain,(
    r1_tarski('#skF_13',k1_tarski('#skF_11')) ),
    inference(resolution,[status(thm)],[c_6,c_1275])).

tff(c_1325,plain,(
    ! [B_163,A_164] :
      ( k1_tarski(B_163) = A_164
      | k1_xboole_0 = A_164
      | ~ r1_tarski(A_164,k1_tarski(B_163)) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1328,plain,
    ( k1_tarski('#skF_11') = '#skF_13'
    | k1_xboole_0 = '#skF_13' ),
    inference(resolution,[status(thm)],[c_1280,c_1325])).

tff(c_1347,plain,(
    k1_tarski('#skF_11') = '#skF_13' ),
    inference(negUnitSimplification,[status(thm)],[c_961,c_1328])).

tff(c_1368,plain,(
    '#skF_13' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1347,c_120])).

tff(c_960,plain,(
    '#skF_8'('#skF_13') = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_544])).

tff(c_965,plain,
    ( r2_hidden('#skF_11','#skF_13')
    | k1_xboole_0 = '#skF_13' ),
    inference(superposition,[status(thm),theory(equality)],[c_960,c_62])).

tff(c_968,plain,(
    r2_hidden('#skF_11','#skF_13') ),
    inference(negUnitSimplification,[status(thm)],[c_961,c_965])).

tff(c_471,plain,(
    ! [A_100,B_101] :
      ( r2_hidden('#skF_1'(A_100,B_101),A_100)
      | r1_tarski(A_100,B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_333,plain,(
    ! [D_88] :
      ( r2_hidden(D_88,k1_tarski('#skF_11'))
      | ~ r2_hidden(D_88,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_303])).

tff(c_337,plain,(
    ! [D_88] :
      ( D_88 = '#skF_11'
      | ~ r2_hidden(D_88,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_333,c_76])).

tff(c_492,plain,(
    ! [B_101] :
      ( '#skF_1'('#skF_12',B_101) = '#skF_11'
      | r1_tarski('#skF_12',B_101) ) ),
    inference(resolution,[status(thm)],[c_471,c_337])).

tff(c_1344,plain,(
    ! [B_163] :
      ( k1_tarski(B_163) = '#skF_12'
      | k1_xboole_0 = '#skF_12'
      | '#skF_1'('#skF_12',k1_tarski(B_163)) = '#skF_11' ) ),
    inference(resolution,[status(thm)],[c_492,c_1325])).

tff(c_1478,plain,(
    ! [B_169] :
      ( k1_tarski(B_169) = '#skF_12'
      | '#skF_1'('#skF_12',k1_tarski(B_169)) = '#skF_11' ) ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_1344])).

tff(c_1493,plain,
    ( k1_tarski('#skF_11') = '#skF_12'
    | '#skF_1'('#skF_12','#skF_13') = '#skF_11' ),
    inference(superposition,[status(thm),theory(equality)],[c_1347,c_1478])).

tff(c_1497,plain,
    ( '#skF_13' = '#skF_12'
    | '#skF_1'('#skF_12','#skF_13') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1347,c_1493])).

tff(c_1498,plain,(
    '#skF_1'('#skF_12','#skF_13') = '#skF_11' ),
    inference(negUnitSimplification,[status(thm)],[c_1368,c_1497])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1502,plain,
    ( ~ r2_hidden('#skF_11','#skF_13')
    | r1_tarski('#skF_12','#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_1498,c_4])).

tff(c_1509,plain,(
    r1_tarski('#skF_12','#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_968,c_1502])).

tff(c_1376,plain,(
    ! [A_50] :
      ( k1_tarski('#skF_11') = A_50
      | k1_xboole_0 = A_50
      | ~ r1_tarski(A_50,'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1347,c_96])).

tff(c_1737,plain,(
    ! [A_183] :
      ( A_183 = '#skF_13'
      | k1_xboole_0 = A_183
      | ~ r1_tarski(A_183,'#skF_13') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1347,c_1376])).

tff(c_1740,plain,
    ( '#skF_13' = '#skF_12'
    | k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_1509,c_1737])).

tff(c_1760,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_1368,c_1740])).

tff(c_1761,plain,(
    k1_tarski('#skF_11') != '#skF_13' ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_78,plain,(
    ! [C_39] : r2_hidden(C_39,k1_tarski(C_39)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2807,plain,(
    ! [A_3016,B_3017] :
      ( ~ r2_hidden('#skF_1'(A_3016,B_3017),B_3017)
      | r1_tarski(A_3016,B_3017) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2834,plain,(
    ! [A_3067] : r1_tarski(A_3067,A_3067) ),
    inference(resolution,[status(thm)],[c_6,c_2807])).

tff(c_66,plain,(
    ! [A_28,B_29] :
      ( k2_xboole_0(A_28,B_29) = B_29
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2841,plain,(
    ! [A_3117] : k2_xboole_0(A_3117,A_3117) = A_3117 ),
    inference(resolution,[status(thm)],[c_2834,c_66])).

tff(c_1762,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_74,plain,(
    ! [A_34] : k5_xboole_0(A_34,A_34) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1763,plain,(
    ! [A_34] : k5_xboole_0(A_34,A_34) = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1762,c_74])).

tff(c_68,plain,(
    ! [A_30,B_31] : k3_xboole_0(A_30,k2_xboole_0(A_30,B_31)) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2514,plain,(
    ! [A_2165,B_2166] : k5_xboole_0(A_2165,k3_xboole_0(A_2165,B_2166)) = k4_xboole_0(A_2165,B_2166) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2536,plain,(
    ! [A_30,B_31] : k4_xboole_0(A_30,k2_xboole_0(A_30,B_31)) = k5_xboole_0(A_30,A_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_2514])).

tff(c_2542,plain,(
    ! [A_30,B_31] : k4_xboole_0(A_30,k2_xboole_0(A_30,B_31)) = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1763,c_2536])).

tff(c_2921,plain,(
    ! [A_3366] : k4_xboole_0(A_3366,A_3366) = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_2841,c_2542])).

tff(c_46,plain,(
    ! [D_23,B_19,A_18] :
      ( ~ r2_hidden(D_23,B_19)
      | ~ r2_hidden(D_23,k4_xboole_0(A_18,B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3025,plain,(
    ! [D_3667,A_3668] :
      ( ~ r2_hidden(D_3667,A_3668)
      | ~ r2_hidden(D_3667,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2921,c_46])).

tff(c_3047,plain,(
    ! [C_3767] : ~ r2_hidden(C_3767,'#skF_12') ),
    inference(resolution,[status(thm)],[c_78,c_3025])).

tff(c_3061,plain,(
    ! [B_3817] : r1_tarski('#skF_12',B_3817) ),
    inference(resolution,[status(thm)],[c_6,c_3047])).

tff(c_3065,plain,(
    ! [B_3817] : k2_xboole_0('#skF_12',B_3817) = B_3817 ),
    inference(resolution,[status(thm)],[c_3061,c_66])).

tff(c_3067,plain,(
    k1_tarski('#skF_11') = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3065,c_110])).

tff(c_3069,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1761,c_3067])).

tff(c_3070,plain,(
    k1_xboole_0 != '#skF_13' ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_3071,plain,(
    k1_tarski('#skF_11') = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_108,plain,
    ( k1_tarski('#skF_11') != '#skF_13'
    | k1_tarski('#skF_11') != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_3108,plain,(
    '#skF_13' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3071,c_3071,c_108])).

tff(c_3081,plain,(
    k2_xboole_0('#skF_12','#skF_13') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3071,c_110])).

tff(c_3795,plain,(
    ! [D_3881,B_3882,A_3883] :
      ( ~ r2_hidden(D_3881,B_3882)
      | r2_hidden(D_3881,k2_xboole_0(A_3883,B_3882)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3866,plain,(
    ! [D_3887] :
      ( ~ r2_hidden(D_3887,'#skF_13')
      | r2_hidden(D_3887,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3081,c_3795])).

tff(c_4072,plain,(
    ! [B_3898] :
      ( r2_hidden('#skF_1'('#skF_13',B_3898),'#skF_12')
      | r1_tarski('#skF_13',B_3898) ) ),
    inference(resolution,[status(thm)],[c_6,c_3866])).

tff(c_4080,plain,(
    r1_tarski('#skF_13','#skF_12') ),
    inference(resolution,[status(thm)],[c_4072,c_4])).

tff(c_3900,plain,(
    ! [B_3888,A_3889] :
      ( k1_tarski(B_3888) = A_3889
      | k1_xboole_0 = A_3889
      | ~ r1_tarski(A_3889,k1_tarski(B_3888)) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3911,plain,(
    ! [A_3889] :
      ( k1_tarski('#skF_11') = A_3889
      | k1_xboole_0 = A_3889
      | ~ r1_tarski(A_3889,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3071,c_3900])).

tff(c_3916,plain,(
    ! [A_3889] :
      ( A_3889 = '#skF_12'
      | k1_xboole_0 = A_3889
      | ~ r1_tarski(A_3889,'#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3071,c_3911])).

tff(c_4084,plain,
    ( '#skF_13' = '#skF_12'
    | k1_xboole_0 = '#skF_13' ),
    inference(resolution,[status(thm)],[c_4080,c_3916])).

tff(c_4091,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3070,c_3108,c_4084])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:49:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.68/1.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.68/1.84  
% 4.68/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.68/1.85  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_11 > #skF_6 > #skF_8 > #skF_4 > #skF_13 > #skF_5 > #skF_10 > #skF_2 > #skF_7 > #skF_3 > #skF_1 > #skF_9 > #skF_12
% 4.68/1.85  
% 4.68/1.85  %Foreground sorts:
% 4.68/1.85  
% 4.68/1.85  
% 4.68/1.85  %Background operators:
% 4.68/1.85  
% 4.68/1.85  
% 4.68/1.85  %Foreground operators:
% 4.68/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.68/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.68/1.85  tff('#skF_11', type, '#skF_11': $i).
% 4.68/1.85  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 4.68/1.85  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.68/1.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.68/1.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.68/1.85  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.68/1.85  tff('#skF_8', type, '#skF_8': $i > $i).
% 4.68/1.85  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.68/1.85  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.68/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.68/1.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.68/1.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.68/1.85  tff('#skF_13', type, '#skF_13': $i).
% 4.68/1.85  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 4.68/1.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.68/1.85  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.68/1.85  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 4.68/1.85  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.68/1.85  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 4.68/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.68/1.85  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.68/1.85  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.68/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.68/1.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.68/1.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.68/1.85  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.68/1.85  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 4.68/1.85  tff('#skF_12', type, '#skF_12': $i).
% 4.68/1.85  
% 4.88/1.86  tff(f_124, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 4.88/1.86  tff(f_68, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.88/1.86  tff(f_41, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 4.88/1.86  tff(f_89, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 4.88/1.86  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.88/1.86  tff(f_76, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 4.88/1.86  tff(f_50, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.88/1.86  tff(f_103, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.88/1.86  tff(f_74, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.88/1.86  tff(f_82, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.88/1.86  tff(f_70, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.88/1.86  tff(f_60, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.88/1.86  tff(c_106, plain, (k1_tarski('#skF_11')!='#skF_13' | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.88/1.86  tff(c_135, plain, (k1_xboole_0!='#skF_12'), inference(splitLeft, [status(thm)], [c_106])).
% 4.88/1.86  tff(c_62, plain, (![A_24]: (r2_hidden('#skF_8'(A_24), A_24) | k1_xboole_0=A_24)), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.88/1.86  tff(c_110, plain, (k2_xboole_0('#skF_12', '#skF_13')=k1_tarski('#skF_11')), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.88/1.86  tff(c_516, plain, (![D_106, B_107, A_108]: (~r2_hidden(D_106, B_107) | r2_hidden(D_106, k2_xboole_0(A_108, B_107)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.88/1.86  tff(c_529, plain, (![D_109]: (~r2_hidden(D_109, '#skF_13') | r2_hidden(D_109, k1_tarski('#skF_11')))), inference(superposition, [status(thm), theory('equality')], [c_110, c_516])).
% 4.88/1.86  tff(c_76, plain, (![C_39, A_35]: (C_39=A_35 | ~r2_hidden(C_39, k1_tarski(A_35)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.88/1.86  tff(c_534, plain, (![D_110]: (D_110='#skF_11' | ~r2_hidden(D_110, '#skF_13'))), inference(resolution, [status(thm)], [c_529, c_76])).
% 4.88/1.86  tff(c_544, plain, ('#skF_8'('#skF_13')='#skF_11' | k1_xboole_0='#skF_13'), inference(resolution, [status(thm)], [c_62, c_534])).
% 4.88/1.86  tff(c_545, plain, (k1_xboole_0='#skF_13'), inference(splitLeft, [status(thm)], [c_544])).
% 4.88/1.86  tff(c_582, plain, ('#skF_13'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_545, c_135])).
% 4.88/1.86  tff(c_104, plain, (k1_xboole_0!='#skF_13' | k1_tarski('#skF_11')!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.88/1.86  tff(c_120, plain, (k1_tarski('#skF_11')!='#skF_12'), inference(splitLeft, [status(thm)], [c_104])).
% 4.88/1.86  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.88/1.86  tff(c_137, plain, (![A_60, B_61]: (k3_xboole_0(A_60, k2_xboole_0(A_60, B_61))=A_60)), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.88/1.86  tff(c_146, plain, (k3_xboole_0('#skF_12', k1_tarski('#skF_11'))='#skF_12'), inference(superposition, [status(thm), theory('equality')], [c_110, c_137])).
% 4.88/1.86  tff(c_303, plain, (![D_84, B_85, A_86]: (r2_hidden(D_84, B_85) | ~r2_hidden(D_84, k3_xboole_0(A_86, B_85)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.88/1.86  tff(c_312, plain, (![D_84]: (r2_hidden(D_84, k1_tarski('#skF_11')) | ~r2_hidden(D_84, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_146, c_303])).
% 4.88/1.86  tff(c_818, plain, (![A_131, B_132]: (~r2_hidden('#skF_1'(A_131, B_132), B_132) | r1_tarski(A_131, B_132))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.88/1.86  tff(c_890, plain, (![A_136]: (r1_tarski(A_136, k1_tarski('#skF_11')) | ~r2_hidden('#skF_1'(A_136, k1_tarski('#skF_11')), '#skF_12'))), inference(resolution, [status(thm)], [c_312, c_818])).
% 4.88/1.86  tff(c_895, plain, (r1_tarski('#skF_12', k1_tarski('#skF_11'))), inference(resolution, [status(thm)], [c_6, c_890])).
% 4.88/1.86  tff(c_96, plain, (![B_51, A_50]: (k1_tarski(B_51)=A_50 | k1_xboole_0=A_50 | ~r1_tarski(A_50, k1_tarski(B_51)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.88/1.86  tff(c_937, plain, (![B_139, A_140]: (k1_tarski(B_139)=A_140 | A_140='#skF_13' | ~r1_tarski(A_140, k1_tarski(B_139)))), inference(demodulation, [status(thm), theory('equality')], [c_545, c_96])).
% 4.88/1.86  tff(c_940, plain, (k1_tarski('#skF_11')='#skF_12' | '#skF_13'='#skF_12'), inference(resolution, [status(thm)], [c_895, c_937])).
% 4.88/1.86  tff(c_959, plain, $false, inference(negUnitSimplification, [status(thm)], [c_582, c_120, c_940])).
% 4.88/1.86  tff(c_961, plain, (k1_xboole_0!='#skF_13'), inference(splitRight, [status(thm)], [c_544])).
% 4.88/1.86  tff(c_528, plain, (![D_106]: (~r2_hidden(D_106, '#skF_13') | r2_hidden(D_106, k1_tarski('#skF_11')))), inference(superposition, [status(thm), theory('equality')], [c_110, c_516])).
% 4.88/1.86  tff(c_1069, plain, (![A_150, B_151]: (~r2_hidden('#skF_1'(A_150, B_151), B_151) | r1_tarski(A_150, B_151))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.88/1.86  tff(c_1275, plain, (![A_162]: (r1_tarski(A_162, k1_tarski('#skF_11')) | ~r2_hidden('#skF_1'(A_162, k1_tarski('#skF_11')), '#skF_13'))), inference(resolution, [status(thm)], [c_528, c_1069])).
% 4.88/1.86  tff(c_1280, plain, (r1_tarski('#skF_13', k1_tarski('#skF_11'))), inference(resolution, [status(thm)], [c_6, c_1275])).
% 4.88/1.86  tff(c_1325, plain, (![B_163, A_164]: (k1_tarski(B_163)=A_164 | k1_xboole_0=A_164 | ~r1_tarski(A_164, k1_tarski(B_163)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.88/1.86  tff(c_1328, plain, (k1_tarski('#skF_11')='#skF_13' | k1_xboole_0='#skF_13'), inference(resolution, [status(thm)], [c_1280, c_1325])).
% 4.88/1.86  tff(c_1347, plain, (k1_tarski('#skF_11')='#skF_13'), inference(negUnitSimplification, [status(thm)], [c_961, c_1328])).
% 4.88/1.86  tff(c_1368, plain, ('#skF_13'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_1347, c_120])).
% 4.88/1.86  tff(c_960, plain, ('#skF_8'('#skF_13')='#skF_11'), inference(splitRight, [status(thm)], [c_544])).
% 4.88/1.86  tff(c_965, plain, (r2_hidden('#skF_11', '#skF_13') | k1_xboole_0='#skF_13'), inference(superposition, [status(thm), theory('equality')], [c_960, c_62])).
% 4.88/1.86  tff(c_968, plain, (r2_hidden('#skF_11', '#skF_13')), inference(negUnitSimplification, [status(thm)], [c_961, c_965])).
% 4.88/1.86  tff(c_471, plain, (![A_100, B_101]: (r2_hidden('#skF_1'(A_100, B_101), A_100) | r1_tarski(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.88/1.86  tff(c_333, plain, (![D_88]: (r2_hidden(D_88, k1_tarski('#skF_11')) | ~r2_hidden(D_88, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_146, c_303])).
% 4.88/1.86  tff(c_337, plain, (![D_88]: (D_88='#skF_11' | ~r2_hidden(D_88, '#skF_12'))), inference(resolution, [status(thm)], [c_333, c_76])).
% 4.88/1.86  tff(c_492, plain, (![B_101]: ('#skF_1'('#skF_12', B_101)='#skF_11' | r1_tarski('#skF_12', B_101))), inference(resolution, [status(thm)], [c_471, c_337])).
% 4.88/1.86  tff(c_1344, plain, (![B_163]: (k1_tarski(B_163)='#skF_12' | k1_xboole_0='#skF_12' | '#skF_1'('#skF_12', k1_tarski(B_163))='#skF_11')), inference(resolution, [status(thm)], [c_492, c_1325])).
% 4.88/1.86  tff(c_1478, plain, (![B_169]: (k1_tarski(B_169)='#skF_12' | '#skF_1'('#skF_12', k1_tarski(B_169))='#skF_11')), inference(negUnitSimplification, [status(thm)], [c_135, c_1344])).
% 4.88/1.86  tff(c_1493, plain, (k1_tarski('#skF_11')='#skF_12' | '#skF_1'('#skF_12', '#skF_13')='#skF_11'), inference(superposition, [status(thm), theory('equality')], [c_1347, c_1478])).
% 4.88/1.86  tff(c_1497, plain, ('#skF_13'='#skF_12' | '#skF_1'('#skF_12', '#skF_13')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_1347, c_1493])).
% 4.88/1.86  tff(c_1498, plain, ('#skF_1'('#skF_12', '#skF_13')='#skF_11'), inference(negUnitSimplification, [status(thm)], [c_1368, c_1497])).
% 4.88/1.86  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.88/1.86  tff(c_1502, plain, (~r2_hidden('#skF_11', '#skF_13') | r1_tarski('#skF_12', '#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_1498, c_4])).
% 4.88/1.86  tff(c_1509, plain, (r1_tarski('#skF_12', '#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_968, c_1502])).
% 4.88/1.86  tff(c_1376, plain, (![A_50]: (k1_tarski('#skF_11')=A_50 | k1_xboole_0=A_50 | ~r1_tarski(A_50, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_1347, c_96])).
% 4.88/1.86  tff(c_1737, plain, (![A_183]: (A_183='#skF_13' | k1_xboole_0=A_183 | ~r1_tarski(A_183, '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_1347, c_1376])).
% 4.88/1.86  tff(c_1740, plain, ('#skF_13'='#skF_12' | k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_1509, c_1737])).
% 4.88/1.86  tff(c_1760, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135, c_1368, c_1740])).
% 4.88/1.86  tff(c_1761, plain, (k1_tarski('#skF_11')!='#skF_13'), inference(splitRight, [status(thm)], [c_106])).
% 4.88/1.86  tff(c_78, plain, (![C_39]: (r2_hidden(C_39, k1_tarski(C_39)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.88/1.86  tff(c_2807, plain, (![A_3016, B_3017]: (~r2_hidden('#skF_1'(A_3016, B_3017), B_3017) | r1_tarski(A_3016, B_3017))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.88/1.86  tff(c_2834, plain, (![A_3067]: (r1_tarski(A_3067, A_3067))), inference(resolution, [status(thm)], [c_6, c_2807])).
% 4.88/1.86  tff(c_66, plain, (![A_28, B_29]: (k2_xboole_0(A_28, B_29)=B_29 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.88/1.86  tff(c_2841, plain, (![A_3117]: (k2_xboole_0(A_3117, A_3117)=A_3117)), inference(resolution, [status(thm)], [c_2834, c_66])).
% 4.88/1.86  tff(c_1762, plain, (k1_xboole_0='#skF_12'), inference(splitRight, [status(thm)], [c_106])).
% 4.88/1.86  tff(c_74, plain, (![A_34]: (k5_xboole_0(A_34, A_34)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.88/1.86  tff(c_1763, plain, (![A_34]: (k5_xboole_0(A_34, A_34)='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_1762, c_74])).
% 4.88/1.86  tff(c_68, plain, (![A_30, B_31]: (k3_xboole_0(A_30, k2_xboole_0(A_30, B_31))=A_30)), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.88/1.86  tff(c_2514, plain, (![A_2165, B_2166]: (k5_xboole_0(A_2165, k3_xboole_0(A_2165, B_2166))=k4_xboole_0(A_2165, B_2166))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.88/1.86  tff(c_2536, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k2_xboole_0(A_30, B_31))=k5_xboole_0(A_30, A_30))), inference(superposition, [status(thm), theory('equality')], [c_68, c_2514])).
% 4.88/1.86  tff(c_2542, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k2_xboole_0(A_30, B_31))='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_1763, c_2536])).
% 4.88/1.86  tff(c_2921, plain, (![A_3366]: (k4_xboole_0(A_3366, A_3366)='#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_2841, c_2542])).
% 4.88/1.86  tff(c_46, plain, (![D_23, B_19, A_18]: (~r2_hidden(D_23, B_19) | ~r2_hidden(D_23, k4_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.88/1.86  tff(c_3025, plain, (![D_3667, A_3668]: (~r2_hidden(D_3667, A_3668) | ~r2_hidden(D_3667, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_2921, c_46])).
% 4.88/1.86  tff(c_3047, plain, (![C_3767]: (~r2_hidden(C_3767, '#skF_12'))), inference(resolution, [status(thm)], [c_78, c_3025])).
% 4.88/1.86  tff(c_3061, plain, (![B_3817]: (r1_tarski('#skF_12', B_3817))), inference(resolution, [status(thm)], [c_6, c_3047])).
% 4.88/1.86  tff(c_3065, plain, (![B_3817]: (k2_xboole_0('#skF_12', B_3817)=B_3817)), inference(resolution, [status(thm)], [c_3061, c_66])).
% 4.88/1.86  tff(c_3067, plain, (k1_tarski('#skF_11')='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_3065, c_110])).
% 4.88/1.86  tff(c_3069, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1761, c_3067])).
% 4.88/1.86  tff(c_3070, plain, (k1_xboole_0!='#skF_13'), inference(splitRight, [status(thm)], [c_104])).
% 4.88/1.86  tff(c_3071, plain, (k1_tarski('#skF_11')='#skF_12'), inference(splitRight, [status(thm)], [c_104])).
% 4.88/1.86  tff(c_108, plain, (k1_tarski('#skF_11')!='#skF_13' | k1_tarski('#skF_11')!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.88/1.86  tff(c_3108, plain, ('#skF_13'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_3071, c_3071, c_108])).
% 4.88/1.86  tff(c_3081, plain, (k2_xboole_0('#skF_12', '#skF_13')='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_3071, c_110])).
% 4.88/1.86  tff(c_3795, plain, (![D_3881, B_3882, A_3883]: (~r2_hidden(D_3881, B_3882) | r2_hidden(D_3881, k2_xboole_0(A_3883, B_3882)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.88/1.86  tff(c_3866, plain, (![D_3887]: (~r2_hidden(D_3887, '#skF_13') | r2_hidden(D_3887, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_3081, c_3795])).
% 4.88/1.86  tff(c_4072, plain, (![B_3898]: (r2_hidden('#skF_1'('#skF_13', B_3898), '#skF_12') | r1_tarski('#skF_13', B_3898))), inference(resolution, [status(thm)], [c_6, c_3866])).
% 4.88/1.86  tff(c_4080, plain, (r1_tarski('#skF_13', '#skF_12')), inference(resolution, [status(thm)], [c_4072, c_4])).
% 4.88/1.86  tff(c_3900, plain, (![B_3888, A_3889]: (k1_tarski(B_3888)=A_3889 | k1_xboole_0=A_3889 | ~r1_tarski(A_3889, k1_tarski(B_3888)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.88/1.86  tff(c_3911, plain, (![A_3889]: (k1_tarski('#skF_11')=A_3889 | k1_xboole_0=A_3889 | ~r1_tarski(A_3889, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_3071, c_3900])).
% 4.88/1.86  tff(c_3916, plain, (![A_3889]: (A_3889='#skF_12' | k1_xboole_0=A_3889 | ~r1_tarski(A_3889, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_3071, c_3911])).
% 4.88/1.86  tff(c_4084, plain, ('#skF_13'='#skF_12' | k1_xboole_0='#skF_13'), inference(resolution, [status(thm)], [c_4080, c_3916])).
% 4.88/1.86  tff(c_4091, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3070, c_3108, c_4084])).
% 4.88/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.88/1.86  
% 4.88/1.86  Inference rules
% 4.88/1.86  ----------------------
% 4.88/1.86  #Ref     : 0
% 4.88/1.86  #Sup     : 980
% 4.88/1.86  #Fact    : 0
% 4.88/1.86  #Define  : 0
% 4.88/1.86  #Split   : 6
% 4.88/1.86  #Chain   : 0
% 4.88/1.86  #Close   : 0
% 4.88/1.86  
% 4.88/1.86  Ordering : KBO
% 4.88/1.87  
% 4.88/1.87  Simplification rules
% 4.88/1.87  ----------------------
% 4.88/1.87  #Subsume      : 123
% 4.88/1.87  #Demod        : 268
% 4.88/1.87  #Tautology    : 542
% 4.88/1.87  #SimpNegUnit  : 38
% 4.88/1.87  #BackRed      : 48
% 4.88/1.87  
% 4.88/1.87  #Partial instantiations: 1704
% 4.88/1.87  #Strategies tried      : 1
% 4.88/1.87  
% 4.88/1.87  Timing (in seconds)
% 4.88/1.87  ----------------------
% 4.88/1.87  Preprocessing        : 0.36
% 4.88/1.87  Parsing              : 0.18
% 4.88/1.87  CNF conversion       : 0.03
% 4.88/1.87  Main loop            : 0.74
% 4.88/1.87  Inferencing          : 0.31
% 4.88/1.87  Reduction            : 0.22
% 4.88/1.87  Demodulation         : 0.15
% 4.88/1.87  BG Simplification    : 0.04
% 4.88/1.87  Subsumption          : 0.11
% 4.88/1.87  Abstraction          : 0.03
% 4.88/1.87  MUC search           : 0.00
% 4.88/1.87  Cooper               : 0.00
% 4.88/1.87  Total                : 1.14
% 4.88/1.87  Index Insertion      : 0.00
% 4.88/1.87  Index Deletion       : 0.00
% 4.88/1.87  Index Matching       : 0.00
% 4.88/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
