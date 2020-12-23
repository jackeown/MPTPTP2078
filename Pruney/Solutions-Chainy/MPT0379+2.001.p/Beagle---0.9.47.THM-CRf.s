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
% DateTime   : Thu Dec  3 09:57:01 EST 2020

% Result     : Theorem 18.49s
% Output     : CNFRefutation 18.49s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 281 expanded)
%              Number of leaves         :   37 ( 108 expanded)
%              Depth                    :   12
%              Number of atoms          :  199 ( 893 expanded)
%              Number of equality atoms :   21 (  97 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_enumset1 > k3_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_11 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_13 > #skF_9 > #skF_8 > #skF_5 > #skF_2 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_143,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,A)
       => ! [C] :
            ( m1_subset_1(C,A)
           => ! [D] :
                ( m1_subset_1(D,A)
               => ! [E] :
                    ( m1_subset_1(E,A)
                   => ! [F] :
                        ( m1_subset_1(F,A)
                       => ! [G] :
                            ( m1_subset_1(G,A)
                           => ! [H] :
                                ( m1_subset_1(H,A)
                               => ( A != k1_xboole_0
                                 => m1_subset_1(k5_enumset1(B,C,D,E,F,G,H),k1_zfmisc_1(A)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_117,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ! [C] :
          ( m1_subset_1(C,A)
         => ! [D] :
              ( m1_subset_1(D,A)
             => ! [E] :
                  ( m1_subset_1(E,A)
                 => ! [F] :
                      ( m1_subset_1(F,A)
                     => ( A != k1_xboole_0
                       => m1_subset_1(k3_enumset1(B,C,D,E,F),k1_zfmisc_1(A)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_subset_1)).

tff(f_91,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_88,axiom,(
    ! [A,B,C,D,E,F] :
      ( F = k3_enumset1(A,B,C,D,E)
    <=> ! [G] :
          ( r2_hidden(G,F)
        <=> ~ ( G != A
              & G != B
              & G != C
              & G != D
              & G != E ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_enumset1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_98,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_82,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_86,plain,(
    m1_subset_1('#skF_12','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_127,plain,(
    ! [B_209,A_210] :
      ( v1_xboole_0(B_209)
      | ~ m1_subset_1(B_209,A_210)
      | ~ v1_xboole_0(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_153,plain,
    ( v1_xboole_0('#skF_12')
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_86,c_127])).

tff(c_160,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_153])).

tff(c_84,plain,(
    m1_subset_1('#skF_13','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_32,plain,(
    ! [B_31,A_30] :
      ( r2_hidden(B_31,A_30)
      | ~ m1_subset_1(B_31,A_30)
      | v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_24,plain,(
    ! [A_27,B_28,C_29] :
      ( r1_tarski(k2_tarski(A_27,B_28),C_29)
      | ~ r2_hidden(B_28,C_29)
      | ~ r2_hidden(A_27,C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_96,plain,(
    m1_subset_1('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_94,plain,(
    m1_subset_1('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_92,plain,(
    m1_subset_1('#skF_9','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_90,plain,(
    m1_subset_1('#skF_10','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_88,plain,(
    m1_subset_1('#skF_11','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1800,plain,(
    ! [C_584,D_583,E_582,F_585,A_586,B_581] :
      ( m1_subset_1(k3_enumset1(B_581,C_584,D_583,E_582,F_585),k1_zfmisc_1(A_586))
      | k1_xboole_0 = A_586
      | ~ m1_subset_1(F_585,A_586)
      | ~ m1_subset_1(E_582,A_586)
      | ~ m1_subset_1(D_583,A_586)
      | ~ m1_subset_1(C_584,A_586)
      | ~ m1_subset_1(B_581,A_586) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_74,plain,(
    ! [A_41] : ~ v1_xboole_0(k1_zfmisc_1(A_41)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_210,plain,(
    ! [B_234,A_235] :
      ( r2_hidden(B_234,A_235)
      | ~ m1_subset_1(B_234,A_235)
      | v1_xboole_0(A_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_12,plain,(
    ! [C_26,A_22] :
      ( r1_tarski(C_26,A_22)
      | ~ r2_hidden(C_26,k1_zfmisc_1(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_217,plain,(
    ! [B_234,A_22] :
      ( r1_tarski(B_234,A_22)
      | ~ m1_subset_1(B_234,k1_zfmisc_1(A_22))
      | v1_xboole_0(k1_zfmisc_1(A_22)) ) ),
    inference(resolution,[status(thm)],[c_210,c_12])).

tff(c_224,plain,(
    ! [B_234,A_22] :
      ( r1_tarski(B_234,A_22)
      | ~ m1_subset_1(B_234,k1_zfmisc_1(A_22)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_217])).

tff(c_22053,plain,(
    ! [B_1469,C_1468,E_1467,A_1470,D_1472,F_1471] :
      ( r1_tarski(k3_enumset1(B_1469,C_1468,D_1472,E_1467,F_1471),A_1470)
      | k1_xboole_0 = A_1470
      | ~ m1_subset_1(F_1471,A_1470)
      | ~ m1_subset_1(E_1467,A_1470)
      | ~ m1_subset_1(D_1472,A_1470)
      | ~ m1_subset_1(C_1468,A_1470)
      | ~ m1_subset_1(B_1469,A_1470) ) ),
    inference(resolution,[status(thm)],[c_1800,c_224])).

tff(c_621,plain,(
    ! [F_377,A_379,E_378,G_375,D_374,C_373,B_376] : k2_xboole_0(k3_enumset1(A_379,B_376,C_373,D_374,E_378),k2_tarski(F_377,G_375)) = k5_enumset1(A_379,B_376,C_373,D_374,E_378,F_377,G_375) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(k2_xboole_0(A_5,C_7),B_6)
      | ~ r1_tarski(C_7,B_6)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5557,plain,(
    ! [F_874,B_877,G_875,E_880,A_878,C_876,B_879,D_881] :
      ( r1_tarski(k5_enumset1(A_878,B_879,C_876,D_881,E_880,F_874,G_875),B_877)
      | ~ r1_tarski(k2_tarski(F_874,G_875),B_877)
      | ~ r1_tarski(k3_enumset1(A_878,B_879,C_876,D_881,E_880),B_877) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_621,c_6])).

tff(c_14,plain,(
    ! [C_26,A_22] :
      ( r2_hidden(C_26,k1_zfmisc_1(A_22))
      | ~ r1_tarski(C_26,A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_167,plain,(
    ! [B_221,A_222] :
      ( m1_subset_1(B_221,A_222)
      | ~ r2_hidden(B_221,A_222)
      | v1_xboole_0(A_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_173,plain,(
    ! [C_26,A_22] :
      ( m1_subset_1(C_26,k1_zfmisc_1(A_22))
      | v1_xboole_0(k1_zfmisc_1(A_22))
      | ~ r1_tarski(C_26,A_22) ) ),
    inference(resolution,[status(thm)],[c_14,c_167])).

tff(c_190,plain,(
    ! [C_227,A_228] :
      ( m1_subset_1(C_227,k1_zfmisc_1(A_228))
      | ~ r1_tarski(C_227,A_228) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_173])).

tff(c_80,plain,(
    ~ m1_subset_1(k5_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12','#skF_13'),k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_198,plain,(
    ~ r1_tarski(k5_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12','#skF_13'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_190,c_80])).

tff(c_5625,plain,
    ( ~ r1_tarski(k2_tarski('#skF_12','#skF_13'),'#skF_6')
    | ~ r1_tarski(k3_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_5557,c_198])).

tff(c_5646,plain,(
    ~ r1_tarski(k3_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_5625])).

tff(c_22140,plain,
    ( k1_xboole_0 = '#skF_6'
    | ~ m1_subset_1('#skF_11','#skF_6')
    | ~ m1_subset_1('#skF_10','#skF_6')
    | ~ m1_subset_1('#skF_9','#skF_6')
    | ~ m1_subset_1('#skF_8','#skF_6')
    | ~ m1_subset_1('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_22053,c_5646])).

tff(c_22259,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_92,c_90,c_88,c_22140])).

tff(c_22261,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_22259])).

tff(c_22262,plain,(
    ~ r1_tarski(k2_tarski('#skF_12','#skF_13'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_5625])).

tff(c_22267,plain,
    ( ~ r2_hidden('#skF_13','#skF_6')
    | ~ r2_hidden('#skF_12','#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_22262])).

tff(c_22268,plain,(
    ~ r2_hidden('#skF_12','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_22267])).

tff(c_22274,plain,
    ( ~ m1_subset_1('#skF_12','#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_32,c_22268])).

tff(c_22278,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_22274])).

tff(c_22280,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_22278])).

tff(c_22281,plain,(
    ~ r2_hidden('#skF_13','#skF_6') ),
    inference(splitRight,[status(thm)],[c_22267])).

tff(c_22380,plain,
    ( ~ m1_subset_1('#skF_13','#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_32,c_22281])).

tff(c_22384,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_22380])).

tff(c_22386,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_22384])).

tff(c_22388,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_22460,plain,(
    ! [D_1488,E_1485,A_1487,B_1486,G_1489] : r2_hidden(G_1489,k3_enumset1(A_1487,B_1486,G_1489,D_1488,E_1485)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22468,plain,(
    ! [D_1488,E_1485,A_1487,B_1486,G_1489] : ~ v1_xboole_0(k3_enumset1(A_1487,B_1486,G_1489,D_1488,E_1485)) ),
    inference(resolution,[status(thm)],[c_22460,c_2])).

tff(c_23717,plain,(
    ! [B_1764,A_1769,C_1767,D_1766,F_1768,E_1765] :
      ( m1_subset_1(k3_enumset1(B_1764,C_1767,D_1766,E_1765,F_1768),k1_zfmisc_1(A_1769))
      | k1_xboole_0 = A_1769
      | ~ m1_subset_1(F_1768,A_1769)
      | ~ m1_subset_1(E_1765,A_1769)
      | ~ m1_subset_1(D_1766,A_1769)
      | ~ m1_subset_1(C_1767,A_1769)
      | ~ m1_subset_1(B_1764,A_1769) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22530,plain,(
    ! [C_1533,A_1534,B_1535] :
      ( r2_hidden(C_1533,A_1534)
      | ~ r2_hidden(C_1533,B_1535)
      | ~ m1_subset_1(B_1535,k1_zfmisc_1(A_1534)) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_22560,plain,(
    ! [A_1541,A_1542] :
      ( r2_hidden('#skF_1'(A_1541),A_1542)
      | ~ m1_subset_1(A_1541,k1_zfmisc_1(A_1542))
      | v1_xboole_0(A_1541) ) ),
    inference(resolution,[status(thm)],[c_4,c_22530])).

tff(c_22576,plain,(
    ! [A_1542,A_1541] :
      ( ~ v1_xboole_0(A_1542)
      | ~ m1_subset_1(A_1541,k1_zfmisc_1(A_1542))
      | v1_xboole_0(A_1541) ) ),
    inference(resolution,[status(thm)],[c_22560,c_2])).

tff(c_23759,plain,(
    ! [B_1764,A_1769,C_1767,D_1766,F_1768,E_1765] :
      ( ~ v1_xboole_0(A_1769)
      | v1_xboole_0(k3_enumset1(B_1764,C_1767,D_1766,E_1765,F_1768))
      | k1_xboole_0 = A_1769
      | ~ m1_subset_1(F_1768,A_1769)
      | ~ m1_subset_1(E_1765,A_1769)
      | ~ m1_subset_1(D_1766,A_1769)
      | ~ m1_subset_1(C_1767,A_1769)
      | ~ m1_subset_1(B_1764,A_1769) ) ),
    inference(resolution,[status(thm)],[c_23717,c_22576])).

tff(c_34949,plain,(
    ! [A_2329,D_2325,B_2328,C_2326,E_2330,F_2327] :
      ( ~ v1_xboole_0(A_2329)
      | k1_xboole_0 = A_2329
      | ~ m1_subset_1(F_2327,A_2329)
      | ~ m1_subset_1(E_2330,A_2329)
      | ~ m1_subset_1(D_2325,A_2329)
      | ~ m1_subset_1(C_2326,A_2329)
      | ~ m1_subset_1(B_2328,A_2329) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22468,c_23759])).

tff(c_35005,plain,(
    ! [E_2330,D_2325,C_2326,B_2328] :
      ( ~ v1_xboole_0('#skF_6')
      | k1_xboole_0 = '#skF_6'
      | ~ m1_subset_1(E_2330,'#skF_6')
      | ~ m1_subset_1(D_2325,'#skF_6')
      | ~ m1_subset_1(C_2326,'#skF_6')
      | ~ m1_subset_1(B_2328,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_86,c_34949])).

tff(c_35047,plain,(
    ! [E_2330,D_2325,C_2326,B_2328] :
      ( k1_xboole_0 = '#skF_6'
      | ~ m1_subset_1(E_2330,'#skF_6')
      | ~ m1_subset_1(D_2325,'#skF_6')
      | ~ m1_subset_1(C_2326,'#skF_6')
      | ~ m1_subset_1(B_2328,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22388,c_35005])).

tff(c_35048,plain,(
    ! [E_2330,D_2325,C_2326,B_2328] :
      ( ~ m1_subset_1(E_2330,'#skF_6')
      | ~ m1_subset_1(D_2325,'#skF_6')
      | ~ m1_subset_1(C_2326,'#skF_6')
      | ~ m1_subset_1(B_2328,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_35047])).

tff(c_35073,plain,(
    ! [B_2328] : ~ m1_subset_1(B_2328,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_35048])).

tff(c_35081,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35073,c_86])).

tff(c_35082,plain,(
    ! [D_2325,E_2330,C_2326] :
      ( ~ m1_subset_1(D_2325,'#skF_6')
      | ~ m1_subset_1(E_2330,'#skF_6')
      | ~ m1_subset_1(C_2326,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_35048])).

tff(c_35083,plain,(
    ! [C_2326] : ~ m1_subset_1(C_2326,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_35082])).

tff(c_35091,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35083,c_86])).

tff(c_35092,plain,(
    ! [D_2325,E_2330] :
      ( ~ m1_subset_1(D_2325,'#skF_6')
      | ~ m1_subset_1(E_2330,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_35082])).

tff(c_35093,plain,(
    ! [E_2330] : ~ m1_subset_1(E_2330,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_35092])).

tff(c_35101,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35093,c_86])).

tff(c_35102,plain,(
    ! [D_2325] : ~ m1_subset_1(D_2325,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_35092])).

tff(c_35361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35102,c_86])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:02:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.49/9.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.49/9.14  
% 18.49/9.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.49/9.15  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_enumset1 > k3_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_11 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_13 > #skF_9 > #skF_8 > #skF_5 > #skF_2 > #skF_12 > #skF_4
% 18.49/9.15  
% 18.49/9.15  %Foreground sorts:
% 18.49/9.15  
% 18.49/9.15  
% 18.49/9.15  %Background operators:
% 18.49/9.15  
% 18.49/9.15  
% 18.49/9.15  %Foreground operators:
% 18.49/9.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.49/9.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 18.49/9.15  tff('#skF_11', type, '#skF_11': $i).
% 18.49/9.15  tff('#skF_1', type, '#skF_1': $i > $i).
% 18.49/9.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 18.49/9.15  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 18.49/9.15  tff('#skF_7', type, '#skF_7': $i).
% 18.49/9.15  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 18.49/9.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.49/9.15  tff('#skF_10', type, '#skF_10': $i).
% 18.49/9.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 18.49/9.15  tff('#skF_6', type, '#skF_6': $i).
% 18.49/9.15  tff('#skF_13', type, '#skF_13': $i).
% 18.49/9.15  tff('#skF_9', type, '#skF_9': $i).
% 18.49/9.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 18.49/9.15  tff('#skF_8', type, '#skF_8': $i).
% 18.49/9.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.49/9.15  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i * $i) > $i).
% 18.49/9.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.49/9.15  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 18.49/9.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 18.49/9.15  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 18.49/9.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 18.49/9.15  tff('#skF_12', type, '#skF_12': $i).
% 18.49/9.15  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i) > $i).
% 18.49/9.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 18.49/9.15  
% 18.49/9.16  tff(f_143, negated_conjecture, ~(![A, B]: (m1_subset_1(B, A) => (![C]: (m1_subset_1(C, A) => (![D]: (m1_subset_1(D, A) => (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, A) => (~(A = k1_xboole_0) => m1_subset_1(k5_enumset1(B, C, D, E, F, G, H), k1_zfmisc_1(A))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_subset_1)).
% 18.49/9.16  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 18.49/9.16  tff(f_54, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 18.49/9.16  tff(f_117, axiom, (![A, B]: (m1_subset_1(B, A) => (![C]: (m1_subset_1(C, A) => (![D]: (m1_subset_1(D, A) => (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, A) => (~(A = k1_xboole_0) => m1_subset_1(k3_enumset1(B, C, D, E, F), k1_zfmisc_1(A))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_subset_1)).
% 18.49/9.16  tff(f_91, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 18.49/9.16  tff(f_48, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 18.49/9.16  tff(f_41, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_enumset1)).
% 18.49/9.16  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 18.49/9.16  tff(f_88, axiom, (![A, B, C, D, E, F]: ((F = k3_enumset1(A, B, C, D, E)) <=> (![G]: (r2_hidden(G, F) <=> ~((((~(G = A) & ~(G = B)) & ~(G = C)) & ~(G = D)) & ~(G = E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_enumset1)).
% 18.49/9.16  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 18.49/9.16  tff(f_98, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 18.49/9.16  tff(c_82, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_143])).
% 18.49/9.16  tff(c_86, plain, (m1_subset_1('#skF_12', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_143])).
% 18.49/9.16  tff(c_127, plain, (![B_209, A_210]: (v1_xboole_0(B_209) | ~m1_subset_1(B_209, A_210) | ~v1_xboole_0(A_210))), inference(cnfTransformation, [status(thm)], [f_67])).
% 18.49/9.16  tff(c_153, plain, (v1_xboole_0('#skF_12') | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_86, c_127])).
% 18.49/9.16  tff(c_160, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_153])).
% 18.49/9.16  tff(c_84, plain, (m1_subset_1('#skF_13', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_143])).
% 18.49/9.16  tff(c_32, plain, (![B_31, A_30]: (r2_hidden(B_31, A_30) | ~m1_subset_1(B_31, A_30) | v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_67])).
% 18.49/9.16  tff(c_24, plain, (![A_27, B_28, C_29]: (r1_tarski(k2_tarski(A_27, B_28), C_29) | ~r2_hidden(B_28, C_29) | ~r2_hidden(A_27, C_29))), inference(cnfTransformation, [status(thm)], [f_54])).
% 18.49/9.16  tff(c_96, plain, (m1_subset_1('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_143])).
% 18.49/9.16  tff(c_94, plain, (m1_subset_1('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_143])).
% 18.49/9.16  tff(c_92, plain, (m1_subset_1('#skF_9', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_143])).
% 18.49/9.16  tff(c_90, plain, (m1_subset_1('#skF_10', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_143])).
% 18.49/9.16  tff(c_88, plain, (m1_subset_1('#skF_11', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_143])).
% 18.49/9.16  tff(c_1800, plain, (![C_584, D_583, E_582, F_585, A_586, B_581]: (m1_subset_1(k3_enumset1(B_581, C_584, D_583, E_582, F_585), k1_zfmisc_1(A_586)) | k1_xboole_0=A_586 | ~m1_subset_1(F_585, A_586) | ~m1_subset_1(E_582, A_586) | ~m1_subset_1(D_583, A_586) | ~m1_subset_1(C_584, A_586) | ~m1_subset_1(B_581, A_586))), inference(cnfTransformation, [status(thm)], [f_117])).
% 18.49/9.16  tff(c_74, plain, (![A_41]: (~v1_xboole_0(k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 18.49/9.16  tff(c_210, plain, (![B_234, A_235]: (r2_hidden(B_234, A_235) | ~m1_subset_1(B_234, A_235) | v1_xboole_0(A_235))), inference(cnfTransformation, [status(thm)], [f_67])).
% 18.49/9.16  tff(c_12, plain, (![C_26, A_22]: (r1_tarski(C_26, A_22) | ~r2_hidden(C_26, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 18.49/9.16  tff(c_217, plain, (![B_234, A_22]: (r1_tarski(B_234, A_22) | ~m1_subset_1(B_234, k1_zfmisc_1(A_22)) | v1_xboole_0(k1_zfmisc_1(A_22)))), inference(resolution, [status(thm)], [c_210, c_12])).
% 18.49/9.16  tff(c_224, plain, (![B_234, A_22]: (r1_tarski(B_234, A_22) | ~m1_subset_1(B_234, k1_zfmisc_1(A_22)))), inference(negUnitSimplification, [status(thm)], [c_74, c_217])).
% 18.49/9.16  tff(c_22053, plain, (![B_1469, C_1468, E_1467, A_1470, D_1472, F_1471]: (r1_tarski(k3_enumset1(B_1469, C_1468, D_1472, E_1467, F_1471), A_1470) | k1_xboole_0=A_1470 | ~m1_subset_1(F_1471, A_1470) | ~m1_subset_1(E_1467, A_1470) | ~m1_subset_1(D_1472, A_1470) | ~m1_subset_1(C_1468, A_1470) | ~m1_subset_1(B_1469, A_1470))), inference(resolution, [status(thm)], [c_1800, c_224])).
% 18.49/9.16  tff(c_621, plain, (![F_377, A_379, E_378, G_375, D_374, C_373, B_376]: (k2_xboole_0(k3_enumset1(A_379, B_376, C_373, D_374, E_378), k2_tarski(F_377, G_375))=k5_enumset1(A_379, B_376, C_373, D_374, E_378, F_377, G_375))), inference(cnfTransformation, [status(thm)], [f_41])).
% 18.49/9.16  tff(c_6, plain, (![A_5, C_7, B_6]: (r1_tarski(k2_xboole_0(A_5, C_7), B_6) | ~r1_tarski(C_7, B_6) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 18.49/9.16  tff(c_5557, plain, (![F_874, B_877, G_875, E_880, A_878, C_876, B_879, D_881]: (r1_tarski(k5_enumset1(A_878, B_879, C_876, D_881, E_880, F_874, G_875), B_877) | ~r1_tarski(k2_tarski(F_874, G_875), B_877) | ~r1_tarski(k3_enumset1(A_878, B_879, C_876, D_881, E_880), B_877))), inference(superposition, [status(thm), theory('equality')], [c_621, c_6])).
% 18.49/9.16  tff(c_14, plain, (![C_26, A_22]: (r2_hidden(C_26, k1_zfmisc_1(A_22)) | ~r1_tarski(C_26, A_22))), inference(cnfTransformation, [status(thm)], [f_48])).
% 18.49/9.16  tff(c_167, plain, (![B_221, A_222]: (m1_subset_1(B_221, A_222) | ~r2_hidden(B_221, A_222) | v1_xboole_0(A_222))), inference(cnfTransformation, [status(thm)], [f_67])).
% 18.49/9.16  tff(c_173, plain, (![C_26, A_22]: (m1_subset_1(C_26, k1_zfmisc_1(A_22)) | v1_xboole_0(k1_zfmisc_1(A_22)) | ~r1_tarski(C_26, A_22))), inference(resolution, [status(thm)], [c_14, c_167])).
% 18.49/9.16  tff(c_190, plain, (![C_227, A_228]: (m1_subset_1(C_227, k1_zfmisc_1(A_228)) | ~r1_tarski(C_227, A_228))), inference(negUnitSimplification, [status(thm)], [c_74, c_173])).
% 18.49/9.16  tff(c_80, plain, (~m1_subset_1(k5_enumset1('#skF_7', '#skF_8', '#skF_9', '#skF_10', '#skF_11', '#skF_12', '#skF_13'), k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 18.49/9.16  tff(c_198, plain, (~r1_tarski(k5_enumset1('#skF_7', '#skF_8', '#skF_9', '#skF_10', '#skF_11', '#skF_12', '#skF_13'), '#skF_6')), inference(resolution, [status(thm)], [c_190, c_80])).
% 18.49/9.16  tff(c_5625, plain, (~r1_tarski(k2_tarski('#skF_12', '#skF_13'), '#skF_6') | ~r1_tarski(k3_enumset1('#skF_7', '#skF_8', '#skF_9', '#skF_10', '#skF_11'), '#skF_6')), inference(resolution, [status(thm)], [c_5557, c_198])).
% 18.49/9.16  tff(c_5646, plain, (~r1_tarski(k3_enumset1('#skF_7', '#skF_8', '#skF_9', '#skF_10', '#skF_11'), '#skF_6')), inference(splitLeft, [status(thm)], [c_5625])).
% 18.49/9.16  tff(c_22140, plain, (k1_xboole_0='#skF_6' | ~m1_subset_1('#skF_11', '#skF_6') | ~m1_subset_1('#skF_10', '#skF_6') | ~m1_subset_1('#skF_9', '#skF_6') | ~m1_subset_1('#skF_8', '#skF_6') | ~m1_subset_1('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_22053, c_5646])).
% 18.49/9.16  tff(c_22259, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_92, c_90, c_88, c_22140])).
% 18.49/9.16  tff(c_22261, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_22259])).
% 18.49/9.16  tff(c_22262, plain, (~r1_tarski(k2_tarski('#skF_12', '#skF_13'), '#skF_6')), inference(splitRight, [status(thm)], [c_5625])).
% 18.49/9.16  tff(c_22267, plain, (~r2_hidden('#skF_13', '#skF_6') | ~r2_hidden('#skF_12', '#skF_6')), inference(resolution, [status(thm)], [c_24, c_22262])).
% 18.49/9.16  tff(c_22268, plain, (~r2_hidden('#skF_12', '#skF_6')), inference(splitLeft, [status(thm)], [c_22267])).
% 18.49/9.16  tff(c_22274, plain, (~m1_subset_1('#skF_12', '#skF_6') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_32, c_22268])).
% 18.49/9.16  tff(c_22278, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_22274])).
% 18.49/9.16  tff(c_22280, plain, $false, inference(negUnitSimplification, [status(thm)], [c_160, c_22278])).
% 18.49/9.16  tff(c_22281, plain, (~r2_hidden('#skF_13', '#skF_6')), inference(splitRight, [status(thm)], [c_22267])).
% 18.49/9.16  tff(c_22380, plain, (~m1_subset_1('#skF_13', '#skF_6') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_32, c_22281])).
% 18.49/9.16  tff(c_22384, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_22380])).
% 18.49/9.16  tff(c_22386, plain, $false, inference(negUnitSimplification, [status(thm)], [c_160, c_22384])).
% 18.49/9.16  tff(c_22388, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_153])).
% 18.49/9.16  tff(c_22460, plain, (![D_1488, E_1485, A_1487, B_1486, G_1489]: (r2_hidden(G_1489, k3_enumset1(A_1487, B_1486, G_1489, D_1488, E_1485)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 18.49/9.16  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 18.49/9.16  tff(c_22468, plain, (![D_1488, E_1485, A_1487, B_1486, G_1489]: (~v1_xboole_0(k3_enumset1(A_1487, B_1486, G_1489, D_1488, E_1485)))), inference(resolution, [status(thm)], [c_22460, c_2])).
% 18.49/9.16  tff(c_23717, plain, (![B_1764, A_1769, C_1767, D_1766, F_1768, E_1765]: (m1_subset_1(k3_enumset1(B_1764, C_1767, D_1766, E_1765, F_1768), k1_zfmisc_1(A_1769)) | k1_xboole_0=A_1769 | ~m1_subset_1(F_1768, A_1769) | ~m1_subset_1(E_1765, A_1769) | ~m1_subset_1(D_1766, A_1769) | ~m1_subset_1(C_1767, A_1769) | ~m1_subset_1(B_1764, A_1769))), inference(cnfTransformation, [status(thm)], [f_117])).
% 18.49/9.16  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 18.49/9.16  tff(c_22530, plain, (![C_1533, A_1534, B_1535]: (r2_hidden(C_1533, A_1534) | ~r2_hidden(C_1533, B_1535) | ~m1_subset_1(B_1535, k1_zfmisc_1(A_1534)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 18.49/9.16  tff(c_22560, plain, (![A_1541, A_1542]: (r2_hidden('#skF_1'(A_1541), A_1542) | ~m1_subset_1(A_1541, k1_zfmisc_1(A_1542)) | v1_xboole_0(A_1541))), inference(resolution, [status(thm)], [c_4, c_22530])).
% 18.49/9.16  tff(c_22576, plain, (![A_1542, A_1541]: (~v1_xboole_0(A_1542) | ~m1_subset_1(A_1541, k1_zfmisc_1(A_1542)) | v1_xboole_0(A_1541))), inference(resolution, [status(thm)], [c_22560, c_2])).
% 18.49/9.16  tff(c_23759, plain, (![B_1764, A_1769, C_1767, D_1766, F_1768, E_1765]: (~v1_xboole_0(A_1769) | v1_xboole_0(k3_enumset1(B_1764, C_1767, D_1766, E_1765, F_1768)) | k1_xboole_0=A_1769 | ~m1_subset_1(F_1768, A_1769) | ~m1_subset_1(E_1765, A_1769) | ~m1_subset_1(D_1766, A_1769) | ~m1_subset_1(C_1767, A_1769) | ~m1_subset_1(B_1764, A_1769))), inference(resolution, [status(thm)], [c_23717, c_22576])).
% 18.49/9.16  tff(c_34949, plain, (![A_2329, D_2325, B_2328, C_2326, E_2330, F_2327]: (~v1_xboole_0(A_2329) | k1_xboole_0=A_2329 | ~m1_subset_1(F_2327, A_2329) | ~m1_subset_1(E_2330, A_2329) | ~m1_subset_1(D_2325, A_2329) | ~m1_subset_1(C_2326, A_2329) | ~m1_subset_1(B_2328, A_2329))), inference(negUnitSimplification, [status(thm)], [c_22468, c_23759])).
% 18.49/9.16  tff(c_35005, plain, (![E_2330, D_2325, C_2326, B_2328]: (~v1_xboole_0('#skF_6') | k1_xboole_0='#skF_6' | ~m1_subset_1(E_2330, '#skF_6') | ~m1_subset_1(D_2325, '#skF_6') | ~m1_subset_1(C_2326, '#skF_6') | ~m1_subset_1(B_2328, '#skF_6'))), inference(resolution, [status(thm)], [c_86, c_34949])).
% 18.49/9.16  tff(c_35047, plain, (![E_2330, D_2325, C_2326, B_2328]: (k1_xboole_0='#skF_6' | ~m1_subset_1(E_2330, '#skF_6') | ~m1_subset_1(D_2325, '#skF_6') | ~m1_subset_1(C_2326, '#skF_6') | ~m1_subset_1(B_2328, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_22388, c_35005])).
% 18.49/9.16  tff(c_35048, plain, (![E_2330, D_2325, C_2326, B_2328]: (~m1_subset_1(E_2330, '#skF_6') | ~m1_subset_1(D_2325, '#skF_6') | ~m1_subset_1(C_2326, '#skF_6') | ~m1_subset_1(B_2328, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_82, c_35047])).
% 18.49/9.16  tff(c_35073, plain, (![B_2328]: (~m1_subset_1(B_2328, '#skF_6'))), inference(splitLeft, [status(thm)], [c_35048])).
% 18.49/9.16  tff(c_35081, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35073, c_86])).
% 18.49/9.16  tff(c_35082, plain, (![D_2325, E_2330, C_2326]: (~m1_subset_1(D_2325, '#skF_6') | ~m1_subset_1(E_2330, '#skF_6') | ~m1_subset_1(C_2326, '#skF_6'))), inference(splitRight, [status(thm)], [c_35048])).
% 18.49/9.16  tff(c_35083, plain, (![C_2326]: (~m1_subset_1(C_2326, '#skF_6'))), inference(splitLeft, [status(thm)], [c_35082])).
% 18.49/9.16  tff(c_35091, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35083, c_86])).
% 18.49/9.16  tff(c_35092, plain, (![D_2325, E_2330]: (~m1_subset_1(D_2325, '#skF_6') | ~m1_subset_1(E_2330, '#skF_6'))), inference(splitRight, [status(thm)], [c_35082])).
% 18.49/9.16  tff(c_35093, plain, (![E_2330]: (~m1_subset_1(E_2330, '#skF_6'))), inference(splitLeft, [status(thm)], [c_35092])).
% 18.49/9.16  tff(c_35101, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35093, c_86])).
% 18.49/9.16  tff(c_35102, plain, (![D_2325]: (~m1_subset_1(D_2325, '#skF_6'))), inference(splitRight, [status(thm)], [c_35092])).
% 18.49/9.16  tff(c_35361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35102, c_86])).
% 18.49/9.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.49/9.16  
% 18.49/9.16  Inference rules
% 18.49/9.16  ----------------------
% 18.49/9.16  #Ref     : 0
% 18.49/9.16  #Sup     : 7407
% 18.49/9.16  #Fact    : 60
% 18.49/9.16  #Define  : 0
% 18.49/9.16  #Split   : 24
% 18.49/9.16  #Chain   : 0
% 18.49/9.16  #Close   : 0
% 18.49/9.16  
% 18.49/9.16  Ordering : KBO
% 18.49/9.16  
% 18.49/9.16  Simplification rules
% 18.49/9.16  ----------------------
% 18.49/9.16  #Subsume      : 961
% 18.49/9.16  #Demod        : 93
% 18.49/9.16  #Tautology    : 238
% 18.49/9.16  #SimpNegUnit  : 2527
% 18.49/9.16  #BackRed      : 79
% 18.49/9.16  
% 18.49/9.16  #Partial instantiations: 0
% 18.49/9.16  #Strategies tried      : 1
% 18.49/9.16  
% 18.49/9.16  Timing (in seconds)
% 18.49/9.16  ----------------------
% 18.49/9.17  Preprocessing        : 0.41
% 18.49/9.17  Parsing              : 0.22
% 18.49/9.17  CNF conversion       : 0.04
% 18.49/9.17  Main loop            : 7.87
% 18.49/9.17  Inferencing          : 1.51
% 18.49/9.17  Reduction            : 1.52
% 18.49/9.17  Demodulation         : 0.94
% 18.49/9.17  BG Simplification    : 0.19
% 18.49/9.17  Subsumption          : 4.14
% 18.49/9.17  Abstraction          : 0.39
% 18.49/9.17  MUC search           : 0.00
% 18.49/9.17  Cooper               : 0.00
% 18.49/9.17  Total                : 8.31
% 18.49/9.17  Index Insertion      : 0.00
% 18.49/9.17  Index Deletion       : 0.00
% 18.49/9.17  Index Matching       : 0.00
% 18.49/9.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
