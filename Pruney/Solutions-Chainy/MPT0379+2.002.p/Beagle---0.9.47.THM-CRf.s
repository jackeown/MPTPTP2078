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
% DateTime   : Thu Dec  3 09:57:01 EST 2020

% Result     : Theorem 27.27s
% Output     : CNFRefutation 27.38s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 258 expanded)
%              Number of leaves         :   37 ( 101 expanded)
%              Depth                    :   11
%              Number of atoms          :  214 ( 866 expanded)
%              Number of equality atoms :   21 ( 108 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_enumset1 > k4_enumset1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_11 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_13 > #skF_9 > #skF_8 > #skF_5 > #skF_2 > #skF_4 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_147,negated_conjecture,(
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

tff(f_121,axiom,(
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
                     => ! [G] :
                          ( m1_subset_1(G,A)
                         => ( A != k1_xboole_0
                           => m1_subset_1(k4_enumset1(B,C,D,E,F,G),k1_zfmisc_1(A)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_subset_1)).

tff(f_92,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_89,axiom,(
    ! [A,B,C,D,E,F,G] :
      ( G = k4_enumset1(A,B,C,D,E,F)
    <=> ! [H] :
          ( r2_hidden(H,G)
        <=> ~ ( H != A
              & H != B
              & H != C
              & H != D
              & H != E
              & H != F ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_enumset1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_86,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_98,plain,(
    m1_subset_1('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_96,plain,(
    m1_subset_1('#skF_9','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_94,plain,(
    m1_subset_1('#skF_10','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_92,plain,(
    m1_subset_1('#skF_11','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_90,plain,(
    m1_subset_1('#skF_12','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_88,plain,(
    m1_subset_1('#skF_13','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_1944,plain,(
    ! [B_683,E_685,G_684,D_686,F_689,A_688,C_687] :
      ( m1_subset_1(k4_enumset1(B_683,C_687,D_686,E_685,F_689,G_684),k1_zfmisc_1(A_688))
      | k1_xboole_0 = A_688
      | ~ m1_subset_1(G_684,A_688)
      | ~ m1_subset_1(F_689,A_688)
      | ~ m1_subset_1(E_685,A_688)
      | ~ m1_subset_1(D_686,A_688)
      | ~ m1_subset_1(C_687,A_688)
      | ~ m1_subset_1(B_683,A_688) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_78,plain,(
    ! [A_41] : ~ v1_xboole_0(k1_zfmisc_1(A_41)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_171,plain,(
    ! [B_247,A_248] :
      ( r2_hidden(B_247,A_248)
      | ~ m1_subset_1(B_247,A_248)
      | v1_xboole_0(A_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_12,plain,(
    ! [C_26,A_22] :
      ( r1_tarski(C_26,A_22)
      | ~ r2_hidden(C_26,k1_zfmisc_1(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_175,plain,(
    ! [B_247,A_22] :
      ( r1_tarski(B_247,A_22)
      | ~ m1_subset_1(B_247,k1_zfmisc_1(A_22))
      | v1_xboole_0(k1_zfmisc_1(A_22)) ) ),
    inference(resolution,[status(thm)],[c_171,c_12])).

tff(c_181,plain,(
    ! [B_247,A_22] :
      ( r1_tarski(B_247,A_22)
      | ~ m1_subset_1(B_247,k1_zfmisc_1(A_22)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_175])).

tff(c_28990,plain,(
    ! [E_1716,B_1719,G_1714,F_1717,D_1715,C_1713,A_1718] :
      ( r1_tarski(k4_enumset1(B_1719,C_1713,D_1715,E_1716,F_1717,G_1714),A_1718)
      | k1_xboole_0 = A_1718
      | ~ m1_subset_1(G_1714,A_1718)
      | ~ m1_subset_1(F_1717,A_1718)
      | ~ m1_subset_1(E_1716,A_1718)
      | ~ m1_subset_1(D_1715,A_1718)
      | ~ m1_subset_1(C_1713,A_1718)
      | ~ m1_subset_1(B_1719,A_1718) ) ),
    inference(resolution,[status(thm)],[c_1944,c_181])).

tff(c_114,plain,(
    ! [B_238,A_239] :
      ( v1_xboole_0(B_238)
      | ~ m1_subset_1(B_238,A_239)
      | ~ v1_xboole_0(A_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_136,plain,
    ( v1_xboole_0('#skF_12')
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_90,c_114])).

tff(c_152,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_100,plain,(
    m1_subset_1('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_30,plain,(
    ! [B_30,A_29] :
      ( r2_hidden(B_30,A_29)
      | ~ m1_subset_1(B_30,A_29)
      | v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_26,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(k1_tarski(A_27),B_28)
      | ~ r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_736,plain,(
    ! [F_388,E_390,A_389,D_394,B_391,C_392,G_393] : k2_xboole_0(k1_tarski(A_389),k4_enumset1(B_391,C_392,D_394,E_390,F_388,G_393)) = k5_enumset1(A_389,B_391,C_392,D_394,E_390,F_388,G_393) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(k2_xboole_0(A_5,C_7),B_6)
      | ~ r1_tarski(C_7,B_6)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6310,plain,(
    ! [F_1018,B_1017,A_1021,C_1023,D_1016,E_1022,B_1020,G_1019] :
      ( r1_tarski(k5_enumset1(A_1021,B_1017,C_1023,D_1016,E_1022,F_1018,G_1019),B_1020)
      | ~ r1_tarski(k4_enumset1(B_1017,C_1023,D_1016,E_1022,F_1018,G_1019),B_1020)
      | ~ r1_tarski(k1_tarski(A_1021),B_1020) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_736,c_6])).

tff(c_14,plain,(
    ! [C_26,A_22] :
      ( r2_hidden(C_26,k1_zfmisc_1(A_22))
      | ~ r1_tarski(C_26,A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_189,plain,(
    ! [B_251,A_252] :
      ( m1_subset_1(B_251,A_252)
      | ~ r2_hidden(B_251,A_252)
      | v1_xboole_0(A_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_195,plain,(
    ! [C_26,A_22] :
      ( m1_subset_1(C_26,k1_zfmisc_1(A_22))
      | v1_xboole_0(k1_zfmisc_1(A_22))
      | ~ r1_tarski(C_26,A_22) ) ),
    inference(resolution,[status(thm)],[c_14,c_189])).

tff(c_216,plain,(
    ! [C_254,A_255] :
      ( m1_subset_1(C_254,k1_zfmisc_1(A_255))
      | ~ r1_tarski(C_254,A_255) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_195])).

tff(c_84,plain,(
    ~ m1_subset_1(k5_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12','#skF_13'),k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_228,plain,(
    ~ r1_tarski(k5_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12','#skF_13'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_216,c_84])).

tff(c_6387,plain,
    ( ~ r1_tarski(k4_enumset1('#skF_8','#skF_9','#skF_10','#skF_11','#skF_12','#skF_13'),'#skF_6')
    | ~ r1_tarski(k1_tarski('#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_6310,c_228])).

tff(c_6388,plain,(
    ~ r1_tarski(k1_tarski('#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_6387])).

tff(c_6392,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_6388])).

tff(c_6398,plain,
    ( ~ m1_subset_1('#skF_7','#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_30,c_6392])).

tff(c_6402,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_6398])).

tff(c_6404,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_6402])).

tff(c_6405,plain,(
    ~ r1_tarski(k4_enumset1('#skF_8','#skF_9','#skF_10','#skF_11','#skF_12','#skF_13'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_6387])).

tff(c_29086,plain,
    ( k1_xboole_0 = '#skF_6'
    | ~ m1_subset_1('#skF_13','#skF_6')
    | ~ m1_subset_1('#skF_12','#skF_6')
    | ~ m1_subset_1('#skF_11','#skF_6')
    | ~ m1_subset_1('#skF_10','#skF_6')
    | ~ m1_subset_1('#skF_9','#skF_6')
    | ~ m1_subset_1('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_28990,c_6405])).

tff(c_29225,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_94,c_92,c_90,c_88,c_29086])).

tff(c_29227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_29225])).

tff(c_29229,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_30697,plain,(
    ! [A_2074,B_2069,E_2071,D_2072,C_2073,F_2075,G_2070] :
      ( m1_subset_1(k4_enumset1(B_2069,C_2073,D_2072,E_2071,F_2075,G_2070),k1_zfmisc_1(A_2074))
      | k1_xboole_0 = A_2074
      | ~ m1_subset_1(G_2070,A_2074)
      | ~ m1_subset_1(F_2075,A_2074)
      | ~ m1_subset_1(E_2071,A_2074)
      | ~ m1_subset_1(D_2072,A_2074)
      | ~ m1_subset_1(C_2073,A_2074)
      | ~ m1_subset_1(B_2069,A_2074) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_44,plain,(
    ! [A_31,B_32,F_36,E_35,D_34,H_40] : r2_hidden(H_40,k4_enumset1(A_31,B_32,H_40,D_34,E_35,F_36)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_29408,plain,(
    ! [C_1806,A_1807,B_1808] :
      ( r2_hidden(C_1806,A_1807)
      | ~ r2_hidden(C_1806,B_1808)
      | ~ m1_subset_1(B_1808,k1_zfmisc_1(A_1807)) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_29431,plain,(
    ! [A_31,A_1807,B_32,F_36,E_35,D_34,H_40] :
      ( r2_hidden(H_40,A_1807)
      | ~ m1_subset_1(k4_enumset1(A_31,B_32,H_40,D_34,E_35,F_36),k1_zfmisc_1(A_1807)) ) ),
    inference(resolution,[status(thm)],[c_44,c_29408])).

tff(c_56760,plain,(
    ! [E_3003,D_3004,G_3005,C_3001,F_3006,A_3002,B_3000] :
      ( r2_hidden(D_3004,A_3002)
      | k1_xboole_0 = A_3002
      | ~ m1_subset_1(G_3005,A_3002)
      | ~ m1_subset_1(F_3006,A_3002)
      | ~ m1_subset_1(E_3003,A_3002)
      | ~ m1_subset_1(D_3004,A_3002)
      | ~ m1_subset_1(C_3001,A_3002)
      | ~ m1_subset_1(B_3000,A_3002) ) ),
    inference(resolution,[status(thm)],[c_30697,c_29431])).

tff(c_56824,plain,(
    ! [E_3003,D_3004,C_3001,F_3006,B_3000] :
      ( r2_hidden(D_3004,'#skF_6')
      | k1_xboole_0 = '#skF_6'
      | ~ m1_subset_1(F_3006,'#skF_6')
      | ~ m1_subset_1(E_3003,'#skF_6')
      | ~ m1_subset_1(D_3004,'#skF_6')
      | ~ m1_subset_1(C_3001,'#skF_6')
      | ~ m1_subset_1(B_3000,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_90,c_56760])).

tff(c_56870,plain,(
    ! [E_3003,D_3004,C_3001,F_3006,B_3000] :
      ( r2_hidden(D_3004,'#skF_6')
      | ~ m1_subset_1(F_3006,'#skF_6')
      | ~ m1_subset_1(E_3003,'#skF_6')
      | ~ m1_subset_1(D_3004,'#skF_6')
      | ~ m1_subset_1(C_3001,'#skF_6')
      | ~ m1_subset_1(B_3000,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_56824])).

tff(c_56889,plain,(
    ! [B_3000] : ~ m1_subset_1(B_3000,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_56870])).

tff(c_56897,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56889,c_90])).

tff(c_56898,plain,(
    ! [F_3006,E_3003,C_3001,D_3004] :
      ( ~ m1_subset_1(F_3006,'#skF_6')
      | ~ m1_subset_1(E_3003,'#skF_6')
      | ~ m1_subset_1(C_3001,'#skF_6')
      | r2_hidden(D_3004,'#skF_6')
      | ~ m1_subset_1(D_3004,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_56870])).

tff(c_56899,plain,(
    ! [C_3001] : ~ m1_subset_1(C_3001,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_56898])).

tff(c_56908,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56899,c_90])).

tff(c_56909,plain,(
    ! [F_3006,E_3003,D_3004] :
      ( ~ m1_subset_1(F_3006,'#skF_6')
      | ~ m1_subset_1(E_3003,'#skF_6')
      | r2_hidden(D_3004,'#skF_6')
      | ~ m1_subset_1(D_3004,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_56898])).

tff(c_56910,plain,(
    ! [E_3003] : ~ m1_subset_1(E_3003,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_56909])).

tff(c_56918,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56910,c_90])).

tff(c_56919,plain,(
    ! [F_3006,D_3004] :
      ( ~ m1_subset_1(F_3006,'#skF_6')
      | r2_hidden(D_3004,'#skF_6')
      | ~ m1_subset_1(D_3004,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_56909])).

tff(c_56920,plain,(
    ! [F_3006] : ~ m1_subset_1(F_3006,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_56919])).

tff(c_56928,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56920,c_90])).

tff(c_57059,plain,(
    ! [D_3014] :
      ( r2_hidden(D_3014,'#skF_6')
      | ~ m1_subset_1(D_3014,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_56919])).

tff(c_29876,plain,(
    ! [F_1870,D_1876,A_1871,G_1875,B_1873,C_1874,E_1872] : k2_xboole_0(k1_tarski(A_1871),k4_enumset1(B_1873,C_1874,D_1876,E_1872,F_1870,G_1875)) = k5_enumset1(A_1871,B_1873,C_1874,D_1876,E_1872,F_1870,G_1875) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_34916,plain,(
    ! [G_2330,B_2328,B_2325,A_2326,D_2327,E_2329,C_2332,F_2331] :
      ( r1_tarski(k5_enumset1(A_2326,B_2325,C_2332,D_2327,E_2329,F_2331,G_2330),B_2328)
      | ~ r1_tarski(k4_enumset1(B_2325,C_2332,D_2327,E_2329,F_2331,G_2330),B_2328)
      | ~ r1_tarski(k1_tarski(A_2326),B_2328) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29876,c_6])).

tff(c_29278,plain,(
    ! [B_1729,A_1730] :
      ( m1_subset_1(B_1729,A_1730)
      | ~ r2_hidden(B_1729,A_1730)
      | v1_xboole_0(A_1730) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_29284,plain,(
    ! [C_26,A_22] :
      ( m1_subset_1(C_26,k1_zfmisc_1(A_22))
      | v1_xboole_0(k1_zfmisc_1(A_22))
      | ~ r1_tarski(C_26,A_22) ) ),
    inference(resolution,[status(thm)],[c_14,c_29278])).

tff(c_29305,plain,(
    ! [C_1732,A_1733] :
      ( m1_subset_1(C_1732,k1_zfmisc_1(A_1733))
      | ~ r1_tarski(C_1732,A_1733) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_29284])).

tff(c_29317,plain,(
    ~ r1_tarski(k5_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12','#skF_13'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_29305,c_84])).

tff(c_34998,plain,
    ( ~ r1_tarski(k4_enumset1('#skF_8','#skF_9','#skF_10','#skF_11','#skF_12','#skF_13'),'#skF_6')
    | ~ r1_tarski(k1_tarski('#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_34916,c_29317])).

tff(c_34999,plain,(
    ~ r1_tarski(k1_tarski('#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_34998])).

tff(c_35003,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_34999])).

tff(c_57071,plain,(
    ~ m1_subset_1('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_57059,c_35003])).

tff(c_57121,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_57071])).

tff(c_57123,plain,(
    r1_tarski(k1_tarski('#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_34998])).

tff(c_24,plain,(
    ! [A_27,B_28] :
      ( r2_hidden(A_27,B_28)
      | ~ r1_tarski(k1_tarski(A_27),B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_57182,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_57123,c_24])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_57190,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_57182,c_2])).

tff(c_57197,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_29229,c_57190])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:05:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 27.27/16.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.27/16.90  
% 27.27/16.90  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.38/16.91  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_enumset1 > k4_enumset1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_11 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_13 > #skF_9 > #skF_8 > #skF_5 > #skF_2 > #skF_4 > #skF_12
% 27.38/16.91  
% 27.38/16.91  %Foreground sorts:
% 27.38/16.91  
% 27.38/16.91  
% 27.38/16.91  %Background operators:
% 27.38/16.91  
% 27.38/16.91  
% 27.38/16.91  %Foreground operators:
% 27.38/16.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 27.38/16.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 27.38/16.91  tff('#skF_11', type, '#skF_11': $i).
% 27.38/16.91  tff(k1_tarski, type, k1_tarski: $i > $i).
% 27.38/16.91  tff('#skF_1', type, '#skF_1': $i > $i).
% 27.38/16.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 27.38/16.91  tff('#skF_7', type, '#skF_7': $i).
% 27.38/16.91  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 27.38/16.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 27.38/16.91  tff('#skF_10', type, '#skF_10': $i).
% 27.38/16.91  tff('#skF_6', type, '#skF_6': $i).
% 27.38/16.91  tff('#skF_13', type, '#skF_13': $i).
% 27.38/16.91  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 27.38/16.91  tff('#skF_9', type, '#skF_9': $i).
% 27.38/16.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 27.38/16.91  tff('#skF_8', type, '#skF_8': $i).
% 27.38/16.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 27.38/16.91  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 27.38/16.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 27.38/16.91  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 27.38/16.91  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 27.38/16.91  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 27.38/16.91  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 27.38/16.91  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 27.38/16.91  tff('#skF_12', type, '#skF_12': $i).
% 27.38/16.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 27.38/16.91  
% 27.38/16.93  tff(f_147, negated_conjecture, ~(![A, B]: (m1_subset_1(B, A) => (![C]: (m1_subset_1(C, A) => (![D]: (m1_subset_1(D, A) => (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, A) => (~(A = k1_xboole_0) => m1_subset_1(k5_enumset1(B, C, D, E, F, G, H), k1_zfmisc_1(A))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_subset_1)).
% 27.38/16.93  tff(f_121, axiom, (![A, B]: (m1_subset_1(B, A) => (![C]: (m1_subset_1(C, A) => (![D]: (m1_subset_1(D, A) => (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, A) => (~(A = k1_xboole_0) => m1_subset_1(k4_enumset1(B, C, D, E, F, G), k1_zfmisc_1(A))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_subset_1)).
% 27.38/16.93  tff(f_92, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 27.38/16.93  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 27.38/16.93  tff(f_48, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 27.38/16.93  tff(f_52, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 27.38/16.93  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_enumset1)).
% 27.38/16.93  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 27.38/16.93  tff(f_89, axiom, (![A, B, C, D, E, F, G]: ((G = k4_enumset1(A, B, C, D, E, F)) <=> (![H]: (r2_hidden(H, G) <=> ~(((((~(H = A) & ~(H = B)) & ~(H = C)) & ~(H = D)) & ~(H = E)) & ~(H = F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_enumset1)).
% 27.38/16.93  tff(f_99, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 27.38/16.93  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 27.38/16.93  tff(c_86, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_147])).
% 27.38/16.93  tff(c_98, plain, (m1_subset_1('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_147])).
% 27.38/16.93  tff(c_96, plain, (m1_subset_1('#skF_9', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_147])).
% 27.38/16.93  tff(c_94, plain, (m1_subset_1('#skF_10', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_147])).
% 27.38/16.93  tff(c_92, plain, (m1_subset_1('#skF_11', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_147])).
% 27.38/16.93  tff(c_90, plain, (m1_subset_1('#skF_12', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_147])).
% 27.38/16.93  tff(c_88, plain, (m1_subset_1('#skF_13', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_147])).
% 27.38/16.93  tff(c_1944, plain, (![B_683, E_685, G_684, D_686, F_689, A_688, C_687]: (m1_subset_1(k4_enumset1(B_683, C_687, D_686, E_685, F_689, G_684), k1_zfmisc_1(A_688)) | k1_xboole_0=A_688 | ~m1_subset_1(G_684, A_688) | ~m1_subset_1(F_689, A_688) | ~m1_subset_1(E_685, A_688) | ~m1_subset_1(D_686, A_688) | ~m1_subset_1(C_687, A_688) | ~m1_subset_1(B_683, A_688))), inference(cnfTransformation, [status(thm)], [f_121])).
% 27.38/16.93  tff(c_78, plain, (![A_41]: (~v1_xboole_0(k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 27.38/16.93  tff(c_171, plain, (![B_247, A_248]: (r2_hidden(B_247, A_248) | ~m1_subset_1(B_247, A_248) | v1_xboole_0(A_248))), inference(cnfTransformation, [status(thm)], [f_65])).
% 27.38/16.93  tff(c_12, plain, (![C_26, A_22]: (r1_tarski(C_26, A_22) | ~r2_hidden(C_26, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 27.38/16.93  tff(c_175, plain, (![B_247, A_22]: (r1_tarski(B_247, A_22) | ~m1_subset_1(B_247, k1_zfmisc_1(A_22)) | v1_xboole_0(k1_zfmisc_1(A_22)))), inference(resolution, [status(thm)], [c_171, c_12])).
% 27.38/16.93  tff(c_181, plain, (![B_247, A_22]: (r1_tarski(B_247, A_22) | ~m1_subset_1(B_247, k1_zfmisc_1(A_22)))), inference(negUnitSimplification, [status(thm)], [c_78, c_175])).
% 27.38/16.93  tff(c_28990, plain, (![E_1716, B_1719, G_1714, F_1717, D_1715, C_1713, A_1718]: (r1_tarski(k4_enumset1(B_1719, C_1713, D_1715, E_1716, F_1717, G_1714), A_1718) | k1_xboole_0=A_1718 | ~m1_subset_1(G_1714, A_1718) | ~m1_subset_1(F_1717, A_1718) | ~m1_subset_1(E_1716, A_1718) | ~m1_subset_1(D_1715, A_1718) | ~m1_subset_1(C_1713, A_1718) | ~m1_subset_1(B_1719, A_1718))), inference(resolution, [status(thm)], [c_1944, c_181])).
% 27.38/16.93  tff(c_114, plain, (![B_238, A_239]: (v1_xboole_0(B_238) | ~m1_subset_1(B_238, A_239) | ~v1_xboole_0(A_239))), inference(cnfTransformation, [status(thm)], [f_65])).
% 27.38/16.93  tff(c_136, plain, (v1_xboole_0('#skF_12') | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_90, c_114])).
% 27.38/16.93  tff(c_152, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_136])).
% 27.38/16.93  tff(c_100, plain, (m1_subset_1('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_147])).
% 27.38/16.93  tff(c_30, plain, (![B_30, A_29]: (r2_hidden(B_30, A_29) | ~m1_subset_1(B_30, A_29) | v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_65])).
% 27.38/16.93  tff(c_26, plain, (![A_27, B_28]: (r1_tarski(k1_tarski(A_27), B_28) | ~r2_hidden(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_52])).
% 27.38/16.93  tff(c_736, plain, (![F_388, E_390, A_389, D_394, B_391, C_392, G_393]: (k2_xboole_0(k1_tarski(A_389), k4_enumset1(B_391, C_392, D_394, E_390, F_388, G_393))=k5_enumset1(A_389, B_391, C_392, D_394, E_390, F_388, G_393))), inference(cnfTransformation, [status(thm)], [f_39])).
% 27.38/16.93  tff(c_6, plain, (![A_5, C_7, B_6]: (r1_tarski(k2_xboole_0(A_5, C_7), B_6) | ~r1_tarski(C_7, B_6) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 27.38/16.93  tff(c_6310, plain, (![F_1018, B_1017, A_1021, C_1023, D_1016, E_1022, B_1020, G_1019]: (r1_tarski(k5_enumset1(A_1021, B_1017, C_1023, D_1016, E_1022, F_1018, G_1019), B_1020) | ~r1_tarski(k4_enumset1(B_1017, C_1023, D_1016, E_1022, F_1018, G_1019), B_1020) | ~r1_tarski(k1_tarski(A_1021), B_1020))), inference(superposition, [status(thm), theory('equality')], [c_736, c_6])).
% 27.38/16.93  tff(c_14, plain, (![C_26, A_22]: (r2_hidden(C_26, k1_zfmisc_1(A_22)) | ~r1_tarski(C_26, A_22))), inference(cnfTransformation, [status(thm)], [f_48])).
% 27.38/16.93  tff(c_189, plain, (![B_251, A_252]: (m1_subset_1(B_251, A_252) | ~r2_hidden(B_251, A_252) | v1_xboole_0(A_252))), inference(cnfTransformation, [status(thm)], [f_65])).
% 27.38/16.93  tff(c_195, plain, (![C_26, A_22]: (m1_subset_1(C_26, k1_zfmisc_1(A_22)) | v1_xboole_0(k1_zfmisc_1(A_22)) | ~r1_tarski(C_26, A_22))), inference(resolution, [status(thm)], [c_14, c_189])).
% 27.38/16.93  tff(c_216, plain, (![C_254, A_255]: (m1_subset_1(C_254, k1_zfmisc_1(A_255)) | ~r1_tarski(C_254, A_255))), inference(negUnitSimplification, [status(thm)], [c_78, c_195])).
% 27.38/16.93  tff(c_84, plain, (~m1_subset_1(k5_enumset1('#skF_7', '#skF_8', '#skF_9', '#skF_10', '#skF_11', '#skF_12', '#skF_13'), k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_147])).
% 27.38/16.93  tff(c_228, plain, (~r1_tarski(k5_enumset1('#skF_7', '#skF_8', '#skF_9', '#skF_10', '#skF_11', '#skF_12', '#skF_13'), '#skF_6')), inference(resolution, [status(thm)], [c_216, c_84])).
% 27.38/16.93  tff(c_6387, plain, (~r1_tarski(k4_enumset1('#skF_8', '#skF_9', '#skF_10', '#skF_11', '#skF_12', '#skF_13'), '#skF_6') | ~r1_tarski(k1_tarski('#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_6310, c_228])).
% 27.38/16.93  tff(c_6388, plain, (~r1_tarski(k1_tarski('#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_6387])).
% 27.38/16.93  tff(c_6392, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_26, c_6388])).
% 27.38/16.93  tff(c_6398, plain, (~m1_subset_1('#skF_7', '#skF_6') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_30, c_6392])).
% 27.38/16.93  tff(c_6402, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_6398])).
% 27.38/16.93  tff(c_6404, plain, $false, inference(negUnitSimplification, [status(thm)], [c_152, c_6402])).
% 27.38/16.93  tff(c_6405, plain, (~r1_tarski(k4_enumset1('#skF_8', '#skF_9', '#skF_10', '#skF_11', '#skF_12', '#skF_13'), '#skF_6')), inference(splitRight, [status(thm)], [c_6387])).
% 27.38/16.93  tff(c_29086, plain, (k1_xboole_0='#skF_6' | ~m1_subset_1('#skF_13', '#skF_6') | ~m1_subset_1('#skF_12', '#skF_6') | ~m1_subset_1('#skF_11', '#skF_6') | ~m1_subset_1('#skF_10', '#skF_6') | ~m1_subset_1('#skF_9', '#skF_6') | ~m1_subset_1('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_28990, c_6405])).
% 27.38/16.93  tff(c_29225, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_94, c_92, c_90, c_88, c_29086])).
% 27.38/16.93  tff(c_29227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_29225])).
% 27.38/16.93  tff(c_29229, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_136])).
% 27.38/16.93  tff(c_30697, plain, (![A_2074, B_2069, E_2071, D_2072, C_2073, F_2075, G_2070]: (m1_subset_1(k4_enumset1(B_2069, C_2073, D_2072, E_2071, F_2075, G_2070), k1_zfmisc_1(A_2074)) | k1_xboole_0=A_2074 | ~m1_subset_1(G_2070, A_2074) | ~m1_subset_1(F_2075, A_2074) | ~m1_subset_1(E_2071, A_2074) | ~m1_subset_1(D_2072, A_2074) | ~m1_subset_1(C_2073, A_2074) | ~m1_subset_1(B_2069, A_2074))), inference(cnfTransformation, [status(thm)], [f_121])).
% 27.38/16.93  tff(c_44, plain, (![A_31, B_32, F_36, E_35, D_34, H_40]: (r2_hidden(H_40, k4_enumset1(A_31, B_32, H_40, D_34, E_35, F_36)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 27.38/16.93  tff(c_29408, plain, (![C_1806, A_1807, B_1808]: (r2_hidden(C_1806, A_1807) | ~r2_hidden(C_1806, B_1808) | ~m1_subset_1(B_1808, k1_zfmisc_1(A_1807)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 27.38/16.93  tff(c_29431, plain, (![A_31, A_1807, B_32, F_36, E_35, D_34, H_40]: (r2_hidden(H_40, A_1807) | ~m1_subset_1(k4_enumset1(A_31, B_32, H_40, D_34, E_35, F_36), k1_zfmisc_1(A_1807)))), inference(resolution, [status(thm)], [c_44, c_29408])).
% 27.38/16.93  tff(c_56760, plain, (![E_3003, D_3004, G_3005, C_3001, F_3006, A_3002, B_3000]: (r2_hidden(D_3004, A_3002) | k1_xboole_0=A_3002 | ~m1_subset_1(G_3005, A_3002) | ~m1_subset_1(F_3006, A_3002) | ~m1_subset_1(E_3003, A_3002) | ~m1_subset_1(D_3004, A_3002) | ~m1_subset_1(C_3001, A_3002) | ~m1_subset_1(B_3000, A_3002))), inference(resolution, [status(thm)], [c_30697, c_29431])).
% 27.38/16.93  tff(c_56824, plain, (![E_3003, D_3004, C_3001, F_3006, B_3000]: (r2_hidden(D_3004, '#skF_6') | k1_xboole_0='#skF_6' | ~m1_subset_1(F_3006, '#skF_6') | ~m1_subset_1(E_3003, '#skF_6') | ~m1_subset_1(D_3004, '#skF_6') | ~m1_subset_1(C_3001, '#skF_6') | ~m1_subset_1(B_3000, '#skF_6'))), inference(resolution, [status(thm)], [c_90, c_56760])).
% 27.38/16.93  tff(c_56870, plain, (![E_3003, D_3004, C_3001, F_3006, B_3000]: (r2_hidden(D_3004, '#skF_6') | ~m1_subset_1(F_3006, '#skF_6') | ~m1_subset_1(E_3003, '#skF_6') | ~m1_subset_1(D_3004, '#skF_6') | ~m1_subset_1(C_3001, '#skF_6') | ~m1_subset_1(B_3000, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_86, c_56824])).
% 27.38/16.93  tff(c_56889, plain, (![B_3000]: (~m1_subset_1(B_3000, '#skF_6'))), inference(splitLeft, [status(thm)], [c_56870])).
% 27.38/16.93  tff(c_56897, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56889, c_90])).
% 27.38/16.93  tff(c_56898, plain, (![F_3006, E_3003, C_3001, D_3004]: (~m1_subset_1(F_3006, '#skF_6') | ~m1_subset_1(E_3003, '#skF_6') | ~m1_subset_1(C_3001, '#skF_6') | r2_hidden(D_3004, '#skF_6') | ~m1_subset_1(D_3004, '#skF_6'))), inference(splitRight, [status(thm)], [c_56870])).
% 27.38/16.93  tff(c_56899, plain, (![C_3001]: (~m1_subset_1(C_3001, '#skF_6'))), inference(splitLeft, [status(thm)], [c_56898])).
% 27.38/16.93  tff(c_56908, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56899, c_90])).
% 27.38/16.93  tff(c_56909, plain, (![F_3006, E_3003, D_3004]: (~m1_subset_1(F_3006, '#skF_6') | ~m1_subset_1(E_3003, '#skF_6') | r2_hidden(D_3004, '#skF_6') | ~m1_subset_1(D_3004, '#skF_6'))), inference(splitRight, [status(thm)], [c_56898])).
% 27.38/16.93  tff(c_56910, plain, (![E_3003]: (~m1_subset_1(E_3003, '#skF_6'))), inference(splitLeft, [status(thm)], [c_56909])).
% 27.38/16.93  tff(c_56918, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56910, c_90])).
% 27.38/16.93  tff(c_56919, plain, (![F_3006, D_3004]: (~m1_subset_1(F_3006, '#skF_6') | r2_hidden(D_3004, '#skF_6') | ~m1_subset_1(D_3004, '#skF_6'))), inference(splitRight, [status(thm)], [c_56909])).
% 27.38/16.93  tff(c_56920, plain, (![F_3006]: (~m1_subset_1(F_3006, '#skF_6'))), inference(splitLeft, [status(thm)], [c_56919])).
% 27.38/16.93  tff(c_56928, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56920, c_90])).
% 27.38/16.93  tff(c_57059, plain, (![D_3014]: (r2_hidden(D_3014, '#skF_6') | ~m1_subset_1(D_3014, '#skF_6'))), inference(splitRight, [status(thm)], [c_56919])).
% 27.38/16.93  tff(c_29876, plain, (![F_1870, D_1876, A_1871, G_1875, B_1873, C_1874, E_1872]: (k2_xboole_0(k1_tarski(A_1871), k4_enumset1(B_1873, C_1874, D_1876, E_1872, F_1870, G_1875))=k5_enumset1(A_1871, B_1873, C_1874, D_1876, E_1872, F_1870, G_1875))), inference(cnfTransformation, [status(thm)], [f_39])).
% 27.38/16.93  tff(c_34916, plain, (![G_2330, B_2328, B_2325, A_2326, D_2327, E_2329, C_2332, F_2331]: (r1_tarski(k5_enumset1(A_2326, B_2325, C_2332, D_2327, E_2329, F_2331, G_2330), B_2328) | ~r1_tarski(k4_enumset1(B_2325, C_2332, D_2327, E_2329, F_2331, G_2330), B_2328) | ~r1_tarski(k1_tarski(A_2326), B_2328))), inference(superposition, [status(thm), theory('equality')], [c_29876, c_6])).
% 27.38/16.93  tff(c_29278, plain, (![B_1729, A_1730]: (m1_subset_1(B_1729, A_1730) | ~r2_hidden(B_1729, A_1730) | v1_xboole_0(A_1730))), inference(cnfTransformation, [status(thm)], [f_65])).
% 27.38/16.93  tff(c_29284, plain, (![C_26, A_22]: (m1_subset_1(C_26, k1_zfmisc_1(A_22)) | v1_xboole_0(k1_zfmisc_1(A_22)) | ~r1_tarski(C_26, A_22))), inference(resolution, [status(thm)], [c_14, c_29278])).
% 27.38/16.93  tff(c_29305, plain, (![C_1732, A_1733]: (m1_subset_1(C_1732, k1_zfmisc_1(A_1733)) | ~r1_tarski(C_1732, A_1733))), inference(negUnitSimplification, [status(thm)], [c_78, c_29284])).
% 27.38/16.93  tff(c_29317, plain, (~r1_tarski(k5_enumset1('#skF_7', '#skF_8', '#skF_9', '#skF_10', '#skF_11', '#skF_12', '#skF_13'), '#skF_6')), inference(resolution, [status(thm)], [c_29305, c_84])).
% 27.38/16.93  tff(c_34998, plain, (~r1_tarski(k4_enumset1('#skF_8', '#skF_9', '#skF_10', '#skF_11', '#skF_12', '#skF_13'), '#skF_6') | ~r1_tarski(k1_tarski('#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_34916, c_29317])).
% 27.38/16.93  tff(c_34999, plain, (~r1_tarski(k1_tarski('#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_34998])).
% 27.38/16.93  tff(c_35003, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_26, c_34999])).
% 27.38/16.93  tff(c_57071, plain, (~m1_subset_1('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_57059, c_35003])).
% 27.38/16.93  tff(c_57121, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_57071])).
% 27.38/16.93  tff(c_57123, plain, (r1_tarski(k1_tarski('#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_34998])).
% 27.38/16.93  tff(c_24, plain, (![A_27, B_28]: (r2_hidden(A_27, B_28) | ~r1_tarski(k1_tarski(A_27), B_28))), inference(cnfTransformation, [status(thm)], [f_52])).
% 27.38/16.93  tff(c_57182, plain, (r2_hidden('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_57123, c_24])).
% 27.38/16.93  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 27.38/16.93  tff(c_57190, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_57182, c_2])).
% 27.38/16.93  tff(c_57197, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_29229, c_57190])).
% 27.38/16.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.38/16.93  
% 27.38/16.93  Inference rules
% 27.38/16.93  ----------------------
% 27.38/16.93  #Ref     : 0
% 27.38/16.93  #Sup     : 12436
% 27.38/16.93  #Fact    : 180
% 27.38/16.93  #Define  : 0
% 27.38/16.93  #Split   : 38
% 27.38/16.93  #Chain   : 0
% 27.38/16.93  #Close   : 0
% 27.38/16.93  
% 27.38/16.93  Ordering : KBO
% 27.38/16.93  
% 27.38/16.93  Simplification rules
% 27.38/16.93  ----------------------
% 27.38/16.93  #Subsume      : 1658
% 27.38/16.93  #Demod        : 293
% 27.38/16.93  #Tautology    : 500
% 27.38/16.93  #SimpNegUnit  : 3392
% 27.38/16.93  #BackRed      : 84
% 27.38/16.93  
% 27.38/16.93  #Partial instantiations: 0
% 27.38/16.93  #Strategies tried      : 1
% 27.38/16.93  
% 27.38/16.93  Timing (in seconds)
% 27.38/16.93  ----------------------
% 27.38/16.93  Preprocessing        : 0.39
% 27.38/16.93  Parsing              : 0.18
% 27.38/16.93  CNF conversion       : 0.05
% 27.38/16.93  Main loop            : 15.76
% 27.38/16.93  Inferencing          : 2.64
% 27.38/16.93  Reduction            : 2.72
% 27.38/16.93  Demodulation         : 1.76
% 27.38/16.93  BG Simplification    : 0.38
% 27.38/16.93  Subsumption          : 9.20
% 27.38/16.93  Abstraction          : 0.86
% 27.38/16.93  MUC search           : 0.00
% 27.38/16.93  Cooper               : 0.00
% 27.38/16.93  Total                : 16.20
% 27.38/16.93  Index Insertion      : 0.00
% 27.38/16.93  Index Deletion       : 0.00
% 27.38/16.93  Index Matching       : 0.00
% 27.38/16.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
