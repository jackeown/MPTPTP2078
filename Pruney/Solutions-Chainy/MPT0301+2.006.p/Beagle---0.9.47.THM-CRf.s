%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:40 EST 2020

% Result     : Theorem 8.44s
% Output     : CNFRefutation 8.70s
% Verified   : 
% Statistics : Number of formulae       :  294 (1736 expanded)
%              Number of leaves         :   44 ( 537 expanded)
%              Depth                    :   14
%              Number of atoms          :  433 (3357 expanded)
%              Number of equality atoms :  200 (2294 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_13 > #skF_17 > #skF_6 > #skF_15 > #skF_10 > #skF_12 > #skF_16 > #skF_14 > #skF_11 > #skF_7 > #skF_9 > #skF_3 > #skF_2 > #skF_8 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_13',type,(
    '#skF_13': ( $i * $i * $i * $i ) > $i )).

tff('#skF_17',type,(
    '#skF_17': $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_16',type,(
    '#skF_16': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_66,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_68,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_108,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_111,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_58,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_79,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_77,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_128,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_24,plain,(
    ! [A_17,B_18] : r1_tarski(k3_xboole_0(A_17,B_18),A_17) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_26,plain,(
    ! [A_19] : r1_tarski(k1_xboole_0,A_19) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_7007,plain,(
    ! [B_10316,A_10317] :
      ( B_10316 = A_10317
      | ~ r1_tarski(B_10316,A_10317)
      | ~ r1_tarski(A_10317,B_10316) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_7020,plain,(
    ! [A_10318] :
      ( k1_xboole_0 = A_10318
      | ~ r1_tarski(A_10318,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26,c_7007])).

tff(c_7033,plain,(
    ! [B_18] : k3_xboole_0(k1_xboole_0,B_18) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_7020])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r1_xboole_0(A_6,B_7)
      | k3_xboole_0(A_6,B_7) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_7460,plain,(
    ! [A_10375,B_10376] :
      ( '#skF_4'(A_10375,B_10376) = A_10375
      | r2_hidden('#skF_5'(A_10375,B_10376),B_10376)
      | k1_tarski(A_10375) = B_10376 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_7107,plain,(
    ! [A_10330,B_10331] :
      ( k2_xboole_0(k1_tarski(A_10330),B_10331) = B_10331
      | ~ r2_hidden(A_10330,B_10331) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_76,plain,(
    ! [A_70,B_71] : k2_xboole_0(k1_tarski(A_70),B_71) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_7116,plain,(
    ! [B_10331,A_10330] :
      ( k1_xboole_0 != B_10331
      | ~ r2_hidden(A_10330,B_10331) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7107,c_76])).

tff(c_8449,plain,(
    ! [A_10387] :
      ( k1_xboole_0 != '#skF_15'
      | '#skF_4'(A_10387,'#skF_15') = A_10387
      | k1_tarski(A_10387) = '#skF_15' ) ),
    inference(resolution,[status(thm)],[c_7460,c_7116])).

tff(c_30,plain,(
    ! [C_24] : r2_hidden(C_24,k1_tarski(C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8452,plain,(
    ! [A_10387] :
      ( r2_hidden(A_10387,'#skF_15')
      | k1_xboole_0 != '#skF_15'
      | '#skF_4'(A_10387,'#skF_15') = A_10387 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8449,c_30])).

tff(c_8687,plain,(
    k1_xboole_0 != '#skF_15' ),
    inference(splitLeft,[status(thm)],[c_8452])).

tff(c_16,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_3'(A_13),A_13)
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8247,plain,(
    ! [A_10387] :
      ( k1_xboole_0 != '#skF_14'
      | '#skF_4'(A_10387,'#skF_14') = A_10387
      | k1_tarski(A_10387) = '#skF_14' ) ),
    inference(resolution,[status(thm)],[c_7460,c_7116])).

tff(c_42,plain,(
    ! [A_27] : k2_tarski(A_27,A_27) = k1_tarski(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_7077,plain,(
    ! [A_10324,B_10325] : k2_xboole_0(k1_tarski(A_10324),k1_tarski(B_10325)) = k2_tarski(A_10324,B_10325) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_7088,plain,(
    ! [A_10326,B_10327] : k2_tarski(A_10326,B_10327) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7077,c_76])).

tff(c_7090,plain,(
    ! [A_27] : k1_tarski(A_27) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_7088])).

tff(c_114,plain,(
    ! [A_85] :
      ( r2_hidden('#skF_3'(A_85),A_85)
      | k1_xboole_0 = A_85 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_28,plain,(
    ! [C_24,A_20] :
      ( C_24 = A_20
      | ~ r2_hidden(C_24,k1_tarski(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_119,plain,(
    ! [A_20] :
      ( '#skF_3'(k1_tarski(A_20)) = A_20
      | k1_tarski(A_20) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_114,c_28])).

tff(c_7091,plain,(
    ! [A_20] : '#skF_3'(k1_tarski(A_20)) = A_20 ),
    inference(negUnitSimplification,[status(thm)],[c_7090,c_119])).

tff(c_8250,plain,(
    ! [A_10387] :
      ( A_10387 = '#skF_3'('#skF_14')
      | k1_xboole_0 != '#skF_14'
      | '#skF_4'(A_10387,'#skF_14') = A_10387 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8247,c_7091])).

tff(c_8631,plain,(
    k1_xboole_0 != '#skF_14' ),
    inference(splitLeft,[status(thm)],[c_8250])).

tff(c_7049,plain,(
    ! [B_10322] : k3_xboole_0(k1_xboole_0,B_10322) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_7020])).

tff(c_14,plain,(
    ! [A_8,B_9,C_12] :
      ( ~ r1_xboole_0(A_8,B_9)
      | ~ r2_hidden(C_12,k3_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_7054,plain,(
    ! [B_10322,C_12] :
      ( ~ r1_xboole_0(k1_xboole_0,B_10322)
      | ~ r2_hidden(C_12,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7049,c_14])).

tff(c_7063,plain,(
    ! [C_12] : ~ r2_hidden(C_12,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_7054])).

tff(c_176,plain,(
    ! [B_97,A_98] :
      ( B_97 = A_98
      | ~ r1_tarski(B_97,A_98)
      | ~ r1_tarski(A_98,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_189,plain,(
    ! [A_99] :
      ( k1_xboole_0 = A_99
      | ~ r1_tarski(A_99,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26,c_176])).

tff(c_202,plain,(
    ! [B_18] : k3_xboole_0(k1_xboole_0,B_18) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_189])).

tff(c_80,plain,
    ( k2_zfmisc_1('#skF_14','#skF_15') != k1_xboole_0
    | k1_xboole_0 != '#skF_17' ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_106,plain,(
    k1_xboole_0 != '#skF_17' ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_86,plain,
    ( k1_xboole_0 = '#skF_15'
    | k1_xboole_0 = '#skF_14'
    | k1_xboole_0 != '#skF_16' ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_113,plain,(
    k1_xboole_0 != '#skF_16' ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_294,plain,(
    ! [A_115,B_116,C_117] :
      ( ~ r1_xboole_0(A_115,B_116)
      | ~ r2_hidden(C_117,k3_xboole_0(A_115,B_116)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_301,plain,(
    ! [B_18,C_117] :
      ( ~ r1_xboole_0(k1_xboole_0,B_18)
      | ~ r2_hidden(C_117,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_294])).

tff(c_308,plain,(
    ! [C_117] : ~ r2_hidden(C_117,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_301])).

tff(c_90,plain,
    ( k1_xboole_0 = '#skF_15'
    | k1_xboole_0 = '#skF_14'
    | k2_zfmisc_1('#skF_16','#skF_17') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_141,plain,(
    k2_zfmisc_1('#skF_16','#skF_17') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_2122,plain,(
    ! [E_3125,F_3126,A_3127,B_3128] :
      ( r2_hidden(k4_tarski(E_3125,F_3126),k2_zfmisc_1(A_3127,B_3128))
      | ~ r2_hidden(F_3126,B_3128)
      | ~ r2_hidden(E_3125,A_3127) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2132,plain,(
    ! [E_3125,F_3126] :
      ( r2_hidden(k4_tarski(E_3125,F_3126),k1_xboole_0)
      | ~ r2_hidden(F_3126,'#skF_17')
      | ~ r2_hidden(E_3125,'#skF_16') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_2122])).

tff(c_2135,plain,(
    ! [F_3126,E_3125] :
      ( ~ r2_hidden(F_3126,'#skF_17')
      | ~ r2_hidden(E_3125,'#skF_16') ) ),
    inference(negUnitSimplification,[status(thm)],[c_308,c_2132])).

tff(c_2137,plain,(
    ! [E_3177] : ~ r2_hidden(E_3177,'#skF_16') ),
    inference(splitLeft,[status(thm)],[c_2135])).

tff(c_2157,plain,(
    k1_xboole_0 = '#skF_16' ),
    inference(resolution,[status(thm)],[c_16,c_2137])).

tff(c_2165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_2157])).

tff(c_2167,plain,(
    ! [F_3226] : ~ r2_hidden(F_3226,'#skF_17') ),
    inference(splitRight,[status(thm)],[c_2135])).

tff(c_2187,plain,(
    k1_xboole_0 = '#skF_17' ),
    inference(resolution,[status(thm)],[c_16,c_2167])).

tff(c_2195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_2187])).

tff(c_2207,plain,(
    ! [B_3278] : ~ r1_xboole_0(k1_xboole_0,B_3278) ),
    inference(splitRight,[status(thm)],[c_301])).

tff(c_2211,plain,(
    ! [B_7] : k3_xboole_0(k1_xboole_0,B_7) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_2207])).

tff(c_2215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_2211])).

tff(c_2216,plain,
    ( k1_xboole_0 = '#skF_14'
    | k1_xboole_0 = '#skF_15' ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_2218,plain,(
    k1_xboole_0 = '#skF_15' ),
    inference(splitLeft,[status(thm)],[c_2216])).

tff(c_2227,plain,(
    ! [A_19] : r1_tarski('#skF_15',A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2218,c_26])).

tff(c_2303,plain,(
    ! [B_3297,A_3298] :
      ( B_3297 = A_3298
      | ~ r1_tarski(B_3297,A_3298)
      | ~ r1_tarski(A_3298,B_3297) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2332,plain,(
    ! [A_3301] :
      ( A_3301 = '#skF_15'
      | ~ r1_tarski(A_3301,'#skF_15') ) ),
    inference(resolution,[status(thm)],[c_2227,c_2303])).

tff(c_2347,plain,(
    ! [B_18] : k3_xboole_0('#skF_15',B_18) = '#skF_15' ),
    inference(resolution,[status(thm)],[c_24,c_2332])).

tff(c_2222,plain,(
    ! [A_6,B_7] :
      ( r1_xboole_0(A_6,B_7)
      | k3_xboole_0(A_6,B_7) != '#skF_15' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2218,c_10])).

tff(c_2223,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_3'(A_13),A_13)
      | A_13 = '#skF_15' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2218,c_16])).

tff(c_4456,plain,(
    ! [A_6616,B_6617,D_6618] :
      ( r2_hidden('#skF_11'(A_6616,B_6617,k2_zfmisc_1(A_6616,B_6617),D_6618),B_6617)
      | ~ r2_hidden(D_6618,k2_zfmisc_1(A_6616,B_6617)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2350,plain,(
    ! [B_3302] : k3_xboole_0('#skF_15',B_3302) = '#skF_15' ),
    inference(resolution,[status(thm)],[c_24,c_2332])).

tff(c_2355,plain,(
    ! [B_3302,C_12] :
      ( ~ r1_xboole_0('#skF_15',B_3302)
      | ~ r2_hidden(C_12,'#skF_15') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2350,c_14])).

tff(c_2382,plain,(
    ! [C_12] : ~ r2_hidden(C_12,'#skF_15') ),
    inference(splitLeft,[status(thm)],[c_2355])).

tff(c_4494,plain,(
    ! [D_6667,A_6668] : ~ r2_hidden(D_6667,k2_zfmisc_1(A_6668,'#skF_15')) ),
    inference(resolution,[status(thm)],[c_4456,c_2382])).

tff(c_4538,plain,(
    ! [A_6668] : k2_zfmisc_1(A_6668,'#skF_15') = '#skF_15' ),
    inference(resolution,[status(thm)],[c_2223,c_4494])).

tff(c_88,plain,
    ( k2_zfmisc_1('#skF_14','#skF_15') != k1_xboole_0
    | k2_zfmisc_1('#skF_16','#skF_17') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_140,plain,(
    k2_zfmisc_1('#skF_14','#skF_15') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_2219,plain,(
    k2_zfmisc_1('#skF_14','#skF_15') != '#skF_15' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2218,c_140])).

tff(c_4542,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4538,c_2219])).

tff(c_4544,plain,(
    ! [B_6717] : ~ r1_xboole_0('#skF_15',B_6717) ),
    inference(splitRight,[status(thm)],[c_2355])).

tff(c_4548,plain,(
    ! [B_7] : k3_xboole_0('#skF_15',B_7) != '#skF_15' ),
    inference(resolution,[status(thm)],[c_2222,c_4544])).

tff(c_4552,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2347,c_4548])).

tff(c_4553,plain,(
    k1_xboole_0 = '#skF_14' ),
    inference(splitRight,[status(thm)],[c_2216])).

tff(c_4561,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_3'(A_13),A_13)
      | A_13 = '#skF_14' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4553,c_16])).

tff(c_6896,plain,(
    ! [A_10211,B_10212,D_10213] :
      ( r2_hidden('#skF_10'(A_10211,B_10212,k2_zfmisc_1(A_10211,B_10212),D_10213),A_10211)
      | ~ r2_hidden(D_10213,k2_zfmisc_1(A_10211,B_10212)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4599,plain,(
    ! [A_6729,B_6730] :
      ( k2_xboole_0(k1_tarski(A_6729),B_6730) = B_6730
      | ~ r2_hidden(A_6729,B_6730) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_4564,plain,(
    ! [A_70,B_71] : k2_xboole_0(k1_tarski(A_70),B_71) != '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4553,c_76])).

tff(c_4610,plain,(
    ! [A_6729] : ~ r2_hidden(A_6729,'#skF_14') ),
    inference(superposition,[status(thm),theory(equality)],[c_4599,c_4564])).

tff(c_4700,plain,(
    ! [C_6748,B_6749,A_6750] :
      ( r2_hidden(C_6748,B_6749)
      | ~ r2_hidden(C_6748,A_6750)
      | ~ r1_tarski(A_6750,B_6749) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4851,plain,(
    ! [A_6774,B_6775] :
      ( r2_hidden('#skF_3'(A_6774),B_6775)
      | ~ r1_tarski(A_6774,B_6775)
      | A_6774 = '#skF_14' ) ),
    inference(resolution,[status(thm)],[c_4561,c_4700])).

tff(c_4604,plain,(
    ! [B_6730,A_6729] :
      ( B_6730 != '#skF_14'
      | ~ r2_hidden(A_6729,B_6730) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4599,c_4564])).

tff(c_4887,plain,(
    ! [B_6779,A_6780] :
      ( B_6779 != '#skF_14'
      | ~ r1_tarski(A_6780,B_6779)
      | A_6780 = '#skF_14' ) ),
    inference(resolution,[status(thm)],[c_4851,c_4604])).

tff(c_4911,plain,(
    ! [A_6781,B_6782] :
      ( A_6781 != '#skF_14'
      | k3_xboole_0(A_6781,B_6782) = '#skF_14' ) ),
    inference(resolution,[status(thm)],[c_24,c_4887])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_2'(A_8,B_9),k3_xboole_0(A_8,B_9))
      | r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4926,plain,(
    ! [A_6781,B_6782] :
      ( r2_hidden('#skF_2'(A_6781,B_6782),'#skF_14')
      | r1_xboole_0(A_6781,B_6782)
      | A_6781 != '#skF_14' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4911,c_12])).

tff(c_4941,plain,(
    ! [A_6781,B_6782] :
      ( r1_xboole_0(A_6781,B_6782)
      | A_6781 != '#skF_14' ) ),
    inference(negUnitSimplification,[status(thm)],[c_4610,c_4926])).

tff(c_4929,plain,(
    ! [A_6781,B_6782,C_12] :
      ( ~ r1_xboole_0(A_6781,B_6782)
      | ~ r2_hidden(C_12,'#skF_14')
      | A_6781 != '#skF_14' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4911,c_14])).

tff(c_4978,plain,(
    ! [A_6789,B_6790] :
      ( ~ r1_xboole_0(A_6789,B_6790)
      | A_6789 != '#skF_14' ) ),
    inference(splitLeft,[status(thm)],[c_4929])).

tff(c_4988,plain,(
    ! [A_6781] : A_6781 != '#skF_14' ),
    inference(resolution,[status(thm)],[c_4941,c_4978])).

tff(c_4997,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4988,c_4553])).

tff(c_4998,plain,(
    ! [C_12] : ~ r2_hidden(C_12,'#skF_14') ),
    inference(splitRight,[status(thm)],[c_4929])).

tff(c_6934,plain,(
    ! [D_10262,B_10263] : ~ r2_hidden(D_10262,k2_zfmisc_1('#skF_14',B_10263)) ),
    inference(resolution,[status(thm)],[c_6896,c_4998])).

tff(c_6978,plain,(
    ! [B_10263] : k2_zfmisc_1('#skF_14',B_10263) = '#skF_14' ),
    inference(resolution,[status(thm)],[c_4561,c_6934])).

tff(c_4557,plain,(
    k2_zfmisc_1('#skF_14','#skF_15') != '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4553,c_140])).

tff(c_6982,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6978,c_4557])).

tff(c_6984,plain,(
    k2_zfmisc_1('#skF_14','#skF_15') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_8688,plain,(
    ! [E_12984,F_12985,A_12986,B_12987] :
      ( r2_hidden(k4_tarski(E_12984,F_12985),k2_zfmisc_1(A_12986,B_12987))
      | ~ r2_hidden(F_12985,B_12987)
      | ~ r2_hidden(E_12984,A_12986) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_8698,plain,(
    ! [E_12984,F_12985] :
      ( r2_hidden(k4_tarski(E_12984,F_12985),k1_xboole_0)
      | ~ r2_hidden(F_12985,'#skF_15')
      | ~ r2_hidden(E_12984,'#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6984,c_8688])).

tff(c_8704,plain,(
    ! [F_12985,E_12984] :
      ( ~ r2_hidden(F_12985,'#skF_15')
      | ~ r2_hidden(E_12984,'#skF_14') ) ),
    inference(negUnitSimplification,[status(thm)],[c_7063,c_8698])).

tff(c_8707,plain,(
    ! [E_13084] : ~ r2_hidden(E_13084,'#skF_14') ),
    inference(splitLeft,[status(thm)],[c_8704])).

tff(c_8727,plain,(
    k1_xboole_0 = '#skF_14' ),
    inference(resolution,[status(thm)],[c_16,c_8707])).

tff(c_8735,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8631,c_8727])).

tff(c_8737,plain,(
    ! [F_13133] : ~ r2_hidden(F_13133,'#skF_15') ),
    inference(splitRight,[status(thm)],[c_8704])).

tff(c_8757,plain,(
    k1_xboole_0 = '#skF_15' ),
    inference(resolution,[status(thm)],[c_16,c_8737])).

tff(c_8765,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8687,c_8757])).

tff(c_8767,plain,(
    k1_xboole_0 = '#skF_15' ),
    inference(splitRight,[status(thm)],[c_8452])).

tff(c_8793,plain,(
    '#skF_17' != '#skF_15' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8767,c_106])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8792,plain,(
    '#skF_15' != '#skF_16' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8767,c_113])).

tff(c_8785,plain,(
    ! [C_12] : ~ r2_hidden(C_12,'#skF_15') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8767,c_7063])).

tff(c_6983,plain,(
    k2_zfmisc_1('#skF_16','#skF_17') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_8788,plain,(
    k2_zfmisc_1('#skF_16','#skF_17') = '#skF_15' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8767,c_6983])).

tff(c_44,plain,(
    ! [E_60,F_61,A_28,B_29] :
      ( r2_hidden(k4_tarski(E_60,F_61),k2_zfmisc_1(A_28,B_29))
      | ~ r2_hidden(F_61,B_29)
      | ~ r2_hidden(E_60,A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_8806,plain,(
    ! [E_60,F_61] :
      ( r2_hidden(k4_tarski(E_60,F_61),'#skF_15')
      | ~ r2_hidden(F_61,'#skF_17')
      | ~ r2_hidden(E_60,'#skF_16') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8788,c_44])).

tff(c_8923,plain,(
    ! [F_61,E_60] :
      ( ~ r2_hidden(F_61,'#skF_17')
      | ~ r2_hidden(E_60,'#skF_16') ) ),
    inference(negUnitSimplification,[status(thm)],[c_8785,c_8806])).

tff(c_8925,plain,(
    ! [E_13196] : ~ r2_hidden(E_13196,'#skF_16') ),
    inference(splitLeft,[status(thm)],[c_8923])).

tff(c_8945,plain,(
    ! [B_2] : r1_tarski('#skF_16',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_8925])).

tff(c_7019,plain,(
    ! [A_19] :
      ( k1_xboole_0 = A_19
      | ~ r1_tarski(A_19,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26,c_7007])).

tff(c_9061,plain,(
    ! [A_13208] :
      ( A_13208 = '#skF_15'
      | ~ r1_tarski(A_13208,'#skF_15') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8767,c_8767,c_7019])).

tff(c_9065,plain,(
    '#skF_15' = '#skF_16' ),
    inference(resolution,[status(thm)],[c_8945,c_9061])).

tff(c_9089,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8792,c_9065])).

tff(c_9091,plain,(
    ! [F_13209] : ~ r2_hidden(F_13209,'#skF_17') ),
    inference(splitRight,[status(thm)],[c_8923])).

tff(c_9111,plain,(
    ! [B_2] : r1_tarski('#skF_17',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_9091])).

tff(c_9150,plain,(
    ! [A_13214] :
      ( A_13214 = '#skF_15'
      | ~ r1_tarski(A_13214,'#skF_15') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8767,c_8767,c_7019])).

tff(c_9154,plain,(
    '#skF_17' = '#skF_15' ),
    inference(resolution,[status(thm)],[c_9111,c_9150])).

tff(c_9178,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8793,c_9154])).

tff(c_9180,plain,(
    k1_xboole_0 = '#skF_14' ),
    inference(splitRight,[status(thm)],[c_8250])).

tff(c_9260,plain,(
    '#skF_17' != '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9180,c_106])).

tff(c_9259,plain,(
    '#skF_16' != '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9180,c_113])).

tff(c_9252,plain,(
    ! [C_12] : ~ r2_hidden(C_12,'#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9180,c_7063])).

tff(c_9255,plain,(
    k2_zfmisc_1('#skF_16','#skF_17') = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9180,c_6983])).

tff(c_9306,plain,(
    ! [E_13270,F_13271,A_13272,B_13273] :
      ( r2_hidden(k4_tarski(E_13270,F_13271),k2_zfmisc_1(A_13272,B_13273))
      | ~ r2_hidden(F_13271,B_13273)
      | ~ r2_hidden(E_13270,A_13272) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_9311,plain,(
    ! [E_13270,F_13271] :
      ( r2_hidden(k4_tarski(E_13270,F_13271),'#skF_14')
      | ~ r2_hidden(F_13271,'#skF_17')
      | ~ r2_hidden(E_13270,'#skF_16') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9255,c_9306])).

tff(c_9316,plain,(
    ! [F_13271,E_13270] :
      ( ~ r2_hidden(F_13271,'#skF_17')
      | ~ r2_hidden(E_13270,'#skF_16') ) ),
    inference(negUnitSimplification,[status(thm)],[c_9252,c_9311])).

tff(c_9360,plain,(
    ! [E_13276] : ~ r2_hidden(E_13276,'#skF_16') ),
    inference(splitLeft,[status(thm)],[c_9316])).

tff(c_9375,plain,(
    ! [B_2] : r1_tarski('#skF_16',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_9360])).

tff(c_9486,plain,(
    ! [A_13288] :
      ( A_13288 = '#skF_14'
      | ~ r1_tarski(A_13288,'#skF_14') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9180,c_9180,c_7019])).

tff(c_9490,plain,(
    '#skF_16' = '#skF_14' ),
    inference(resolution,[status(thm)],[c_9375,c_9486])).

tff(c_9514,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9259,c_9490])).

tff(c_9516,plain,(
    ! [F_13289] : ~ r2_hidden(F_13289,'#skF_17') ),
    inference(splitRight,[status(thm)],[c_9316])).

tff(c_9531,plain,(
    ! [B_2] : r1_tarski('#skF_17',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_9516])).

tff(c_9637,plain,(
    ! [A_13299] :
      ( A_13299 = '#skF_14'
      | ~ r1_tarski(A_13299,'#skF_14') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9180,c_9180,c_7019])).

tff(c_9641,plain,(
    '#skF_17' = '#skF_14' ),
    inference(resolution,[status(thm)],[c_9531,c_9637])).

tff(c_9665,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9260,c_9641])).

tff(c_9667,plain,(
    ! [B_13300] : ~ r1_xboole_0(k1_xboole_0,B_13300) ),
    inference(splitRight,[status(thm)],[c_7054])).

tff(c_9671,plain,(
    ! [B_7] : k3_xboole_0(k1_xboole_0,B_7) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_9667])).

tff(c_9675,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7033,c_9671])).

tff(c_9677,plain,(
    k1_xboole_0 = '#skF_16' ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_9680,plain,(
    ! [A_19] : r1_tarski('#skF_16',A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9677,c_26])).

tff(c_9750,plain,(
    ! [B_13317,A_13318] :
      ( B_13317 = A_13318
      | ~ r1_tarski(B_13317,A_13318)
      | ~ r1_tarski(A_13318,B_13317) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_9777,plain,(
    ! [A_13320] :
      ( A_13320 = '#skF_16'
      | ~ r1_tarski(A_13320,'#skF_16') ) ),
    inference(resolution,[status(thm)],[c_9680,c_9750])).

tff(c_9792,plain,(
    ! [B_18] : k3_xboole_0('#skF_16',B_18) = '#skF_16' ),
    inference(resolution,[status(thm)],[c_24,c_9777])).

tff(c_9703,plain,(
    ! [A_6,B_7] :
      ( r1_xboole_0(A_6,B_7)
      | k3_xboole_0(A_6,B_7) != '#skF_16' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9677,c_10])).

tff(c_9696,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_3'(A_13),A_13)
      | A_13 = '#skF_16' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9677,c_16])).

tff(c_12150,plain,(
    ! [A_16792,B_16793,D_16794] :
      ( r2_hidden('#skF_11'(A_16792,B_16793,k2_zfmisc_1(A_16792,B_16793),D_16794),B_16793)
      | ~ r2_hidden(D_16794,k2_zfmisc_1(A_16792,B_16793)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_9828,plain,(
    ! [A_13326,B_13327,C_13328] :
      ( ~ r1_xboole_0(A_13326,B_13327)
      | ~ r2_hidden(C_13328,k3_xboole_0(A_13326,B_13327)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_9831,plain,(
    ! [B_18,C_13328] :
      ( ~ r1_xboole_0('#skF_16',B_18)
      | ~ r2_hidden(C_13328,'#skF_16') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9792,c_9828])).

tff(c_9837,plain,(
    ! [C_13328] : ~ r2_hidden(C_13328,'#skF_16') ),
    inference(splitLeft,[status(thm)],[c_9831])).

tff(c_12188,plain,(
    ! [D_16843,A_16844] : ~ r2_hidden(D_16843,k2_zfmisc_1(A_16844,'#skF_16')) ),
    inference(resolution,[status(thm)],[c_12150,c_9837])).

tff(c_12232,plain,(
    ! [A_16844] : k2_zfmisc_1(A_16844,'#skF_16') = '#skF_16' ),
    inference(resolution,[status(thm)],[c_9696,c_12188])).

tff(c_9676,plain,
    ( k1_xboole_0 = '#skF_14'
    | k1_xboole_0 = '#skF_15' ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_9688,plain,
    ( '#skF_16' = '#skF_14'
    | '#skF_15' = '#skF_16' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9677,c_9677,c_9676])).

tff(c_9689,plain,(
    '#skF_15' = '#skF_16' ),
    inference(splitLeft,[status(thm)],[c_9688])).

tff(c_84,plain,
    ( k2_zfmisc_1('#skF_14','#skF_15') != k1_xboole_0
    | k1_xboole_0 != '#skF_16' ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_9686,plain,(
    k2_zfmisc_1('#skF_14','#skF_15') != '#skF_16' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9677,c_9677,c_84])).

tff(c_9690,plain,(
    k2_zfmisc_1('#skF_14','#skF_16') != '#skF_16' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9689,c_9686])).

tff(c_12236,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12232,c_9690])).

tff(c_12238,plain,(
    ! [B_16893] : ~ r1_xboole_0('#skF_16',B_16893) ),
    inference(splitRight,[status(thm)],[c_9831])).

tff(c_12242,plain,(
    ! [B_7] : k3_xboole_0('#skF_16',B_7) != '#skF_16' ),
    inference(resolution,[status(thm)],[c_9703,c_12238])).

tff(c_12246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9792,c_12242])).

tff(c_12247,plain,(
    '#skF_16' = '#skF_14' ),
    inference(splitRight,[status(thm)],[c_9688])).

tff(c_12253,plain,(
    k1_xboole_0 = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12247,c_9677])).

tff(c_12266,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_3'(A_13),A_13)
      | A_13 = '#skF_14' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12253,c_16])).

tff(c_14411,plain,(
    ! [A_20083,B_20084,D_20085] :
      ( r2_hidden('#skF_10'(A_20083,B_20084,k2_zfmisc_1(A_20083,B_20084),D_20085),A_20083)
      | ~ r2_hidden(D_20085,k2_zfmisc_1(A_20083,B_20084)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_12297,plain,(
    ! [A_16903,B_16904] :
      ( k2_xboole_0(k1_tarski(A_16903),B_16904) = B_16904
      | ~ r2_hidden(A_16903,B_16904) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_9679,plain,(
    ! [A_70,B_71] : k2_xboole_0(k1_tarski(A_70),B_71) != '#skF_16' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9677,c_76])).

tff(c_12264,plain,(
    ! [A_70,B_71] : k2_xboole_0(k1_tarski(A_70),B_71) != '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12247,c_9679])).

tff(c_12308,plain,(
    ! [A_16903] : ~ r2_hidden(A_16903,'#skF_14') ),
    inference(superposition,[status(thm),theory(equality)],[c_12297,c_12264])).

tff(c_12419,plain,(
    ! [C_16928,B_16929,A_16930] :
      ( r2_hidden(C_16928,B_16929)
      | ~ r2_hidden(C_16928,A_16930)
      | ~ r1_tarski(A_16930,B_16929) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12550,plain,(
    ! [A_16950,B_16951] :
      ( r2_hidden('#skF_3'(A_16950),B_16951)
      | ~ r1_tarski(A_16950,B_16951)
      | A_16950 = '#skF_14' ) ),
    inference(resolution,[status(thm)],[c_12266,c_12419])).

tff(c_12302,plain,(
    ! [B_16904,A_16903] :
      ( B_16904 != '#skF_14'
      | ~ r2_hidden(A_16903,B_16904) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12297,c_12264])).

tff(c_12578,plain,(
    ! [B_16952,A_16953] :
      ( B_16952 != '#skF_14'
      | ~ r1_tarski(A_16953,B_16952)
      | A_16953 = '#skF_14' ) ),
    inference(resolution,[status(thm)],[c_12550,c_12302])).

tff(c_12602,plain,(
    ! [A_16954,B_16955] :
      ( A_16954 != '#skF_14'
      | k3_xboole_0(A_16954,B_16955) = '#skF_14' ) ),
    inference(resolution,[status(thm)],[c_24,c_12578])).

tff(c_12611,plain,(
    ! [A_16954,B_16955] :
      ( r2_hidden('#skF_2'(A_16954,B_16955),'#skF_14')
      | r1_xboole_0(A_16954,B_16955)
      | A_16954 != '#skF_14' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12602,c_12])).

tff(c_12631,plain,(
    ! [A_16954,B_16955] :
      ( r1_xboole_0(A_16954,B_16955)
      | A_16954 != '#skF_14' ) ),
    inference(negUnitSimplification,[status(thm)],[c_12308,c_12611])).

tff(c_12620,plain,(
    ! [A_16954,B_16955,C_12] :
      ( ~ r1_xboole_0(A_16954,B_16955)
      | ~ r2_hidden(C_12,'#skF_14')
      | A_16954 != '#skF_14' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12602,c_14])).

tff(c_12676,plain,(
    ! [A_16963,B_16964] :
      ( ~ r1_xboole_0(A_16963,B_16964)
      | A_16963 != '#skF_14' ) ),
    inference(splitLeft,[status(thm)],[c_12620])).

tff(c_12686,plain,(
    ! [A_16954] : A_16954 != '#skF_14' ),
    inference(resolution,[status(thm)],[c_12631,c_12676])).

tff(c_12696,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12686,c_12253])).

tff(c_12697,plain,(
    ! [C_12] : ~ r2_hidden(C_12,'#skF_14') ),
    inference(splitRight,[status(thm)],[c_12620])).

tff(c_14441,plain,(
    ! [D_20134,B_20135] : ~ r2_hidden(D_20134,k2_zfmisc_1('#skF_14',B_20135)) ),
    inference(resolution,[status(thm)],[c_14411,c_12697])).

tff(c_14477,plain,(
    ! [B_20135] : k2_zfmisc_1('#skF_14',B_20135) = '#skF_14' ),
    inference(resolution,[status(thm)],[c_12266,c_14441])).

tff(c_12252,plain,(
    k2_zfmisc_1('#skF_14','#skF_15') != '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12247,c_9686])).

tff(c_14481,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14477,c_12252])).

tff(c_14483,plain,(
    k1_xboole_0 = '#skF_17' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_82,plain,
    ( k1_xboole_0 = '#skF_15'
    | k1_xboole_0 = '#skF_14'
    | k1_xboole_0 != '#skF_17' ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_14499,plain,
    ( '#skF_17' = '#skF_15'
    | '#skF_17' = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14483,c_14483,c_14483,c_82])).

tff(c_14500,plain,(
    '#skF_17' = '#skF_14' ),
    inference(splitLeft,[status(thm)],[c_14499])).

tff(c_14496,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_3'(A_13),A_13)
      | A_13 = '#skF_17' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14483,c_16])).

tff(c_14501,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_3'(A_13),A_13)
      | A_13 = '#skF_14' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14500,c_14496])).

tff(c_16746,plain,(
    ! [A_23426,B_23427,D_23428] :
      ( r2_hidden('#skF_10'(A_23426,B_23427,k2_zfmisc_1(A_23426,B_23427),D_23428),A_23426)
      | ~ r2_hidden(D_23428,k2_zfmisc_1(A_23426,B_23427)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_14560,plain,(
    ! [A_20201,B_20202] :
      ( k2_xboole_0(k1_tarski(A_20201),B_20202) = B_20202
      | ~ r2_hidden(A_20201,B_20202) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_14484,plain,(
    ! [A_70,B_71] : k2_xboole_0(k1_tarski(A_70),B_71) != '#skF_17' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14483,c_76])).

tff(c_14502,plain,(
    ! [A_70,B_71] : k2_xboole_0(k1_tarski(A_70),B_71) != '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14500,c_14484])).

tff(c_14571,plain,(
    ! [A_20201] : ~ r2_hidden(A_20201,'#skF_14') ),
    inference(superposition,[status(thm),theory(equality)],[c_14560,c_14502])).

tff(c_14691,plain,(
    ! [C_20226,B_20227,A_20228] :
      ( r2_hidden(C_20226,B_20227)
      | ~ r2_hidden(C_20226,A_20228)
      | ~ r1_tarski(A_20228,B_20227) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14806,plain,(
    ! [A_20244,B_20245] :
      ( r2_hidden('#skF_3'(A_20244),B_20245)
      | ~ r1_tarski(A_20244,B_20245)
      | A_20244 = '#skF_14' ) ),
    inference(resolution,[status(thm)],[c_14501,c_14691])).

tff(c_14565,plain,(
    ! [B_20202,A_20201] :
      ( B_20202 != '#skF_14'
      | ~ r2_hidden(A_20201,B_20202) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14560,c_14502])).

tff(c_14842,plain,(
    ! [B_20249,A_20250] :
      ( B_20249 != '#skF_14'
      | ~ r1_tarski(A_20250,B_20249)
      | A_20250 = '#skF_14' ) ),
    inference(resolution,[status(thm)],[c_14806,c_14565])).

tff(c_14866,plain,(
    ! [A_20251,B_20252] :
      ( A_20251 != '#skF_14'
      | k3_xboole_0(A_20251,B_20252) = '#skF_14' ) ),
    inference(resolution,[status(thm)],[c_24,c_14842])).

tff(c_14875,plain,(
    ! [A_20251,B_20252] :
      ( r2_hidden('#skF_2'(A_20251,B_20252),'#skF_14')
      | r1_xboole_0(A_20251,B_20252)
      | A_20251 != '#skF_14' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14866,c_12])).

tff(c_14895,plain,(
    ! [A_20251,B_20252] :
      ( r1_xboole_0(A_20251,B_20252)
      | A_20251 != '#skF_14' ) ),
    inference(negUnitSimplification,[status(thm)],[c_14571,c_14875])).

tff(c_14884,plain,(
    ! [A_20251,B_20252,C_12] :
      ( ~ r1_xboole_0(A_20251,B_20252)
      | ~ r2_hidden(C_12,'#skF_14')
      | A_20251 != '#skF_14' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14866,c_14])).

tff(c_14933,plain,(
    ! [A_20259,B_20260] :
      ( ~ r1_xboole_0(A_20259,B_20260)
      | A_20259 != '#skF_14' ) ),
    inference(splitLeft,[status(thm)],[c_14884])).

tff(c_14943,plain,(
    ! [A_20251] : A_20251 != '#skF_14' ),
    inference(resolution,[status(thm)],[c_14895,c_14933])).

tff(c_14506,plain,(
    k1_xboole_0 = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14500,c_14483])).

tff(c_14953,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14943,c_14506])).

tff(c_14954,plain,(
    ! [C_12] : ~ r2_hidden(C_12,'#skF_14') ),
    inference(splitRight,[status(thm)],[c_14884])).

tff(c_16780,plain,(
    ! [D_23477,B_23478] : ~ r2_hidden(D_23477,k2_zfmisc_1('#skF_14',B_23478)) ),
    inference(resolution,[status(thm)],[c_16746,c_14954])).

tff(c_16824,plain,(
    ! [B_23478] : k2_zfmisc_1('#skF_14',B_23478) = '#skF_14' ),
    inference(resolution,[status(thm)],[c_14501,c_16780])).

tff(c_14482,plain,(
    k2_zfmisc_1('#skF_14','#skF_15') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_14493,plain,(
    k2_zfmisc_1('#skF_14','#skF_15') != '#skF_17' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14483,c_14482])).

tff(c_14503,plain,(
    k2_zfmisc_1('#skF_14','#skF_15') != '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14500,c_14493])).

tff(c_16828,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16824,c_14503])).

tff(c_16829,plain,(
    '#skF_17' = '#skF_15' ),
    inference(splitRight,[status(thm)],[c_14499])).

tff(c_16831,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_3'(A_13),A_13)
      | A_13 = '#skF_15' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16829,c_14496])).

tff(c_19121,plain,(
    ! [A_26824,B_26825,D_26826] :
      ( r2_hidden('#skF_11'(A_26824,B_26825,k2_zfmisc_1(A_26824,B_26825),D_26826),B_26825)
      | ~ r2_hidden(D_26826,k2_zfmisc_1(A_26824,B_26825)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_16916,plain,(
    ! [A_23546,B_23547] :
      ( k2_xboole_0(k1_tarski(A_23546),B_23547) = B_23547
      | ~ r2_hidden(A_23546,B_23547) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_16832,plain,(
    ! [A_70,B_71] : k2_xboole_0(k1_tarski(A_70),B_71) != '#skF_15' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16829,c_14484])).

tff(c_16934,plain,(
    ! [A_23546] : ~ r2_hidden(A_23546,'#skF_15') ),
    inference(superposition,[status(thm),theory(equality)],[c_16916,c_16832])).

tff(c_17007,plain,(
    ! [C_23563,B_23564,A_23565] :
      ( r2_hidden(C_23563,B_23564)
      | ~ r2_hidden(C_23563,A_23565)
      | ~ r1_tarski(A_23565,B_23564) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_17119,plain,(
    ! [A_23581,B_23582] :
      ( r2_hidden('#skF_3'(A_23581),B_23582)
      | ~ r1_tarski(A_23581,B_23582)
      | A_23581 = '#skF_15' ) ),
    inference(resolution,[status(thm)],[c_16831,c_17007])).

tff(c_16925,plain,(
    ! [B_23547,A_23546] :
      ( B_23547 != '#skF_15'
      | ~ r2_hidden(A_23546,B_23547) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16916,c_16832])).

tff(c_17142,plain,(
    ! [B_23583,A_23584] :
      ( B_23583 != '#skF_15'
      | ~ r1_tarski(A_23584,B_23583)
      | A_23584 = '#skF_15' ) ),
    inference(resolution,[status(thm)],[c_17119,c_16925])).

tff(c_17174,plain,(
    ! [A_23588,B_23589] :
      ( A_23588 != '#skF_15'
      | k3_xboole_0(A_23588,B_23589) = '#skF_15' ) ),
    inference(resolution,[status(thm)],[c_24,c_17142])).

tff(c_17183,plain,(
    ! [A_23588,B_23589] :
      ( r2_hidden('#skF_2'(A_23588,B_23589),'#skF_15')
      | r1_xboole_0(A_23588,B_23589)
      | A_23588 != '#skF_15' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17174,c_12])).

tff(c_17203,plain,(
    ! [A_23588,B_23589] :
      ( r1_xboole_0(A_23588,B_23589)
      | A_23588 != '#skF_15' ) ),
    inference(negUnitSimplification,[status(thm)],[c_16934,c_17183])).

tff(c_17192,plain,(
    ! [A_23588,B_23589,C_12] :
      ( ~ r1_xboole_0(A_23588,B_23589)
      | ~ r2_hidden(C_12,'#skF_15')
      | A_23588 != '#skF_15' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17174,c_14])).

tff(c_17240,plain,(
    ! [A_23594,B_23595] :
      ( ~ r1_xboole_0(A_23594,B_23595)
      | A_23594 != '#skF_15' ) ),
    inference(splitLeft,[status(thm)],[c_17192])).

tff(c_17250,plain,(
    ! [A_23588] : A_23588 != '#skF_15' ),
    inference(resolution,[status(thm)],[c_17203,c_17240])).

tff(c_16836,plain,(
    k1_xboole_0 = '#skF_15' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16829,c_14483])).

tff(c_17261,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17250,c_16836])).

tff(c_17262,plain,(
    ! [C_12] : ~ r2_hidden(C_12,'#skF_15') ),
    inference(splitRight,[status(thm)],[c_17192])).

tff(c_19151,plain,(
    ! [D_26875,A_26876] : ~ r2_hidden(D_26875,k2_zfmisc_1(A_26876,'#skF_15')) ),
    inference(resolution,[status(thm)],[c_19121,c_17262])).

tff(c_19192,plain,(
    ! [A_26876] : k2_zfmisc_1(A_26876,'#skF_15') = '#skF_15' ),
    inference(resolution,[status(thm)],[c_16831,c_19151])).

tff(c_16833,plain,(
    k2_zfmisc_1('#skF_14','#skF_15') != '#skF_15' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16829,c_14493])).

tff(c_19196,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19192,c_16833])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:12:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.44/2.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.44/2.76  
% 8.44/2.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.44/2.76  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_13 > #skF_17 > #skF_6 > #skF_15 > #skF_10 > #skF_12 > #skF_16 > #skF_14 > #skF_11 > #skF_7 > #skF_9 > #skF_3 > #skF_2 > #skF_8 > #skF_1 > #skF_5 > #skF_4
% 8.44/2.76  
% 8.44/2.76  %Foreground sorts:
% 8.44/2.76  
% 8.44/2.76  
% 8.44/2.76  %Background operators:
% 8.44/2.76  
% 8.44/2.76  
% 8.44/2.76  %Foreground operators:
% 8.44/2.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.44/2.76  tff('#skF_13', type, '#skF_13': ($i * $i * $i * $i) > $i).
% 8.44/2.76  tff('#skF_17', type, '#skF_17': $i).
% 8.44/2.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.44/2.76  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 8.44/2.76  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.44/2.76  tff('#skF_15', type, '#skF_15': $i).
% 8.44/2.76  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.44/2.76  tff('#skF_10', type, '#skF_10': ($i * $i * $i * $i) > $i).
% 8.44/2.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.44/2.76  tff('#skF_12', type, '#skF_12': ($i * $i * $i * $i) > $i).
% 8.44/2.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.44/2.76  tff('#skF_16', type, '#skF_16': $i).
% 8.44/2.76  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.44/2.76  tff('#skF_14', type, '#skF_14': $i).
% 8.44/2.76  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.44/2.76  tff('#skF_11', type, '#skF_11': ($i * $i * $i * $i) > $i).
% 8.44/2.76  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 8.44/2.76  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 8.44/2.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.44/2.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.44/2.76  tff('#skF_3', type, '#skF_3': $i > $i).
% 8.44/2.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.44/2.76  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.44/2.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.44/2.76  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 8.44/2.76  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.44/2.76  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.44/2.76  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 8.44/2.76  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.44/2.76  
% 8.70/2.79  tff(f_66, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 8.70/2.79  tff(f_68, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.70/2.79  tff(f_64, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.70/2.79  tff(f_36, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.70/2.79  tff(f_75, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 8.70/2.79  tff(f_108, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 8.70/2.79  tff(f_111, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 8.70/2.79  tff(f_58, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 8.70/2.79  tff(f_79, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 8.70/2.79  tff(f_77, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 8.70/2.79  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 8.70/2.79  tff(f_128, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.70/2.79  tff(f_91, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 8.70/2.79  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.70/2.79  tff(c_24, plain, (![A_17, B_18]: (r1_tarski(k3_xboole_0(A_17, B_18), A_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.70/2.79  tff(c_26, plain, (![A_19]: (r1_tarski(k1_xboole_0, A_19))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.70/2.79  tff(c_7007, plain, (![B_10316, A_10317]: (B_10316=A_10317 | ~r1_tarski(B_10316, A_10317) | ~r1_tarski(A_10317, B_10316))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.70/2.79  tff(c_7020, plain, (![A_10318]: (k1_xboole_0=A_10318 | ~r1_tarski(A_10318, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_7007])).
% 8.70/2.79  tff(c_7033, plain, (![B_18]: (k3_xboole_0(k1_xboole_0, B_18)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_7020])).
% 8.70/2.79  tff(c_10, plain, (![A_6, B_7]: (r1_xboole_0(A_6, B_7) | k3_xboole_0(A_6, B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.70/2.79  tff(c_7460, plain, (![A_10375, B_10376]: ('#skF_4'(A_10375, B_10376)=A_10375 | r2_hidden('#skF_5'(A_10375, B_10376), B_10376) | k1_tarski(A_10375)=B_10376)), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.70/2.79  tff(c_7107, plain, (![A_10330, B_10331]: (k2_xboole_0(k1_tarski(A_10330), B_10331)=B_10331 | ~r2_hidden(A_10330, B_10331))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.70/2.79  tff(c_76, plain, (![A_70, B_71]: (k2_xboole_0(k1_tarski(A_70), B_71)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.70/2.79  tff(c_7116, plain, (![B_10331, A_10330]: (k1_xboole_0!=B_10331 | ~r2_hidden(A_10330, B_10331))), inference(superposition, [status(thm), theory('equality')], [c_7107, c_76])).
% 8.70/2.79  tff(c_8449, plain, (![A_10387]: (k1_xboole_0!='#skF_15' | '#skF_4'(A_10387, '#skF_15')=A_10387 | k1_tarski(A_10387)='#skF_15')), inference(resolution, [status(thm)], [c_7460, c_7116])).
% 8.70/2.79  tff(c_30, plain, (![C_24]: (r2_hidden(C_24, k1_tarski(C_24)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.70/2.79  tff(c_8452, plain, (![A_10387]: (r2_hidden(A_10387, '#skF_15') | k1_xboole_0!='#skF_15' | '#skF_4'(A_10387, '#skF_15')=A_10387)), inference(superposition, [status(thm), theory('equality')], [c_8449, c_30])).
% 8.70/2.79  tff(c_8687, plain, (k1_xboole_0!='#skF_15'), inference(splitLeft, [status(thm)], [c_8452])).
% 8.70/2.79  tff(c_16, plain, (![A_13]: (r2_hidden('#skF_3'(A_13), A_13) | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.70/2.79  tff(c_8247, plain, (![A_10387]: (k1_xboole_0!='#skF_14' | '#skF_4'(A_10387, '#skF_14')=A_10387 | k1_tarski(A_10387)='#skF_14')), inference(resolution, [status(thm)], [c_7460, c_7116])).
% 8.70/2.79  tff(c_42, plain, (![A_27]: (k2_tarski(A_27, A_27)=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.70/2.79  tff(c_7077, plain, (![A_10324, B_10325]: (k2_xboole_0(k1_tarski(A_10324), k1_tarski(B_10325))=k2_tarski(A_10324, B_10325))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.70/2.79  tff(c_7088, plain, (![A_10326, B_10327]: (k2_tarski(A_10326, B_10327)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7077, c_76])).
% 8.70/2.79  tff(c_7090, plain, (![A_27]: (k1_tarski(A_27)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_42, c_7088])).
% 8.70/2.79  tff(c_114, plain, (![A_85]: (r2_hidden('#skF_3'(A_85), A_85) | k1_xboole_0=A_85)), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.70/2.79  tff(c_28, plain, (![C_24, A_20]: (C_24=A_20 | ~r2_hidden(C_24, k1_tarski(A_20)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.70/2.79  tff(c_119, plain, (![A_20]: ('#skF_3'(k1_tarski(A_20))=A_20 | k1_tarski(A_20)=k1_xboole_0)), inference(resolution, [status(thm)], [c_114, c_28])).
% 8.70/2.79  tff(c_7091, plain, (![A_20]: ('#skF_3'(k1_tarski(A_20))=A_20)), inference(negUnitSimplification, [status(thm)], [c_7090, c_119])).
% 8.70/2.79  tff(c_8250, plain, (![A_10387]: (A_10387='#skF_3'('#skF_14') | k1_xboole_0!='#skF_14' | '#skF_4'(A_10387, '#skF_14')=A_10387)), inference(superposition, [status(thm), theory('equality')], [c_8247, c_7091])).
% 8.70/2.79  tff(c_8631, plain, (k1_xboole_0!='#skF_14'), inference(splitLeft, [status(thm)], [c_8250])).
% 8.70/2.79  tff(c_7049, plain, (![B_10322]: (k3_xboole_0(k1_xboole_0, B_10322)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_7020])).
% 8.70/2.79  tff(c_14, plain, (![A_8, B_9, C_12]: (~r1_xboole_0(A_8, B_9) | ~r2_hidden(C_12, k3_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.70/2.79  tff(c_7054, plain, (![B_10322, C_12]: (~r1_xboole_0(k1_xboole_0, B_10322) | ~r2_hidden(C_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_7049, c_14])).
% 8.70/2.79  tff(c_7063, plain, (![C_12]: (~r2_hidden(C_12, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_7054])).
% 8.70/2.79  tff(c_176, plain, (![B_97, A_98]: (B_97=A_98 | ~r1_tarski(B_97, A_98) | ~r1_tarski(A_98, B_97))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.70/2.79  tff(c_189, plain, (![A_99]: (k1_xboole_0=A_99 | ~r1_tarski(A_99, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_176])).
% 8.70/2.79  tff(c_202, plain, (![B_18]: (k3_xboole_0(k1_xboole_0, B_18)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_189])).
% 8.70/2.79  tff(c_80, plain, (k2_zfmisc_1('#skF_14', '#skF_15')!=k1_xboole_0 | k1_xboole_0!='#skF_17'), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.70/2.79  tff(c_106, plain, (k1_xboole_0!='#skF_17'), inference(splitLeft, [status(thm)], [c_80])).
% 8.70/2.79  tff(c_86, plain, (k1_xboole_0='#skF_15' | k1_xboole_0='#skF_14' | k1_xboole_0!='#skF_16'), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.70/2.79  tff(c_113, plain, (k1_xboole_0!='#skF_16'), inference(splitLeft, [status(thm)], [c_86])).
% 8.70/2.79  tff(c_294, plain, (![A_115, B_116, C_117]: (~r1_xboole_0(A_115, B_116) | ~r2_hidden(C_117, k3_xboole_0(A_115, B_116)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.70/2.79  tff(c_301, plain, (![B_18, C_117]: (~r1_xboole_0(k1_xboole_0, B_18) | ~r2_hidden(C_117, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_202, c_294])).
% 8.70/2.79  tff(c_308, plain, (![C_117]: (~r2_hidden(C_117, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_301])).
% 8.70/2.79  tff(c_90, plain, (k1_xboole_0='#skF_15' | k1_xboole_0='#skF_14' | k2_zfmisc_1('#skF_16', '#skF_17')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.70/2.79  tff(c_141, plain, (k2_zfmisc_1('#skF_16', '#skF_17')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_90])).
% 8.70/2.79  tff(c_2122, plain, (![E_3125, F_3126, A_3127, B_3128]: (r2_hidden(k4_tarski(E_3125, F_3126), k2_zfmisc_1(A_3127, B_3128)) | ~r2_hidden(F_3126, B_3128) | ~r2_hidden(E_3125, A_3127))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.70/2.79  tff(c_2132, plain, (![E_3125, F_3126]: (r2_hidden(k4_tarski(E_3125, F_3126), k1_xboole_0) | ~r2_hidden(F_3126, '#skF_17') | ~r2_hidden(E_3125, '#skF_16'))), inference(superposition, [status(thm), theory('equality')], [c_141, c_2122])).
% 8.70/2.79  tff(c_2135, plain, (![F_3126, E_3125]: (~r2_hidden(F_3126, '#skF_17') | ~r2_hidden(E_3125, '#skF_16'))), inference(negUnitSimplification, [status(thm)], [c_308, c_2132])).
% 8.70/2.79  tff(c_2137, plain, (![E_3177]: (~r2_hidden(E_3177, '#skF_16'))), inference(splitLeft, [status(thm)], [c_2135])).
% 8.70/2.79  tff(c_2157, plain, (k1_xboole_0='#skF_16'), inference(resolution, [status(thm)], [c_16, c_2137])).
% 8.70/2.79  tff(c_2165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_113, c_2157])).
% 8.70/2.79  tff(c_2167, plain, (![F_3226]: (~r2_hidden(F_3226, '#skF_17'))), inference(splitRight, [status(thm)], [c_2135])).
% 8.70/2.79  tff(c_2187, plain, (k1_xboole_0='#skF_17'), inference(resolution, [status(thm)], [c_16, c_2167])).
% 8.70/2.79  tff(c_2195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_2187])).
% 8.70/2.79  tff(c_2207, plain, (![B_3278]: (~r1_xboole_0(k1_xboole_0, B_3278))), inference(splitRight, [status(thm)], [c_301])).
% 8.70/2.79  tff(c_2211, plain, (![B_7]: (k3_xboole_0(k1_xboole_0, B_7)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_2207])).
% 8.70/2.79  tff(c_2215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_202, c_2211])).
% 8.70/2.79  tff(c_2216, plain, (k1_xboole_0='#skF_14' | k1_xboole_0='#skF_15'), inference(splitRight, [status(thm)], [c_90])).
% 8.70/2.79  tff(c_2218, plain, (k1_xboole_0='#skF_15'), inference(splitLeft, [status(thm)], [c_2216])).
% 8.70/2.79  tff(c_2227, plain, (![A_19]: (r1_tarski('#skF_15', A_19))), inference(demodulation, [status(thm), theory('equality')], [c_2218, c_26])).
% 8.70/2.79  tff(c_2303, plain, (![B_3297, A_3298]: (B_3297=A_3298 | ~r1_tarski(B_3297, A_3298) | ~r1_tarski(A_3298, B_3297))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.70/2.79  tff(c_2332, plain, (![A_3301]: (A_3301='#skF_15' | ~r1_tarski(A_3301, '#skF_15'))), inference(resolution, [status(thm)], [c_2227, c_2303])).
% 8.70/2.79  tff(c_2347, plain, (![B_18]: (k3_xboole_0('#skF_15', B_18)='#skF_15')), inference(resolution, [status(thm)], [c_24, c_2332])).
% 8.70/2.79  tff(c_2222, plain, (![A_6, B_7]: (r1_xboole_0(A_6, B_7) | k3_xboole_0(A_6, B_7)!='#skF_15')), inference(demodulation, [status(thm), theory('equality')], [c_2218, c_10])).
% 8.70/2.79  tff(c_2223, plain, (![A_13]: (r2_hidden('#skF_3'(A_13), A_13) | A_13='#skF_15')), inference(demodulation, [status(thm), theory('equality')], [c_2218, c_16])).
% 8.70/2.79  tff(c_4456, plain, (![A_6616, B_6617, D_6618]: (r2_hidden('#skF_11'(A_6616, B_6617, k2_zfmisc_1(A_6616, B_6617), D_6618), B_6617) | ~r2_hidden(D_6618, k2_zfmisc_1(A_6616, B_6617)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.70/2.79  tff(c_2350, plain, (![B_3302]: (k3_xboole_0('#skF_15', B_3302)='#skF_15')), inference(resolution, [status(thm)], [c_24, c_2332])).
% 8.70/2.79  tff(c_2355, plain, (![B_3302, C_12]: (~r1_xboole_0('#skF_15', B_3302) | ~r2_hidden(C_12, '#skF_15'))), inference(superposition, [status(thm), theory('equality')], [c_2350, c_14])).
% 8.70/2.79  tff(c_2382, plain, (![C_12]: (~r2_hidden(C_12, '#skF_15'))), inference(splitLeft, [status(thm)], [c_2355])).
% 8.70/2.79  tff(c_4494, plain, (![D_6667, A_6668]: (~r2_hidden(D_6667, k2_zfmisc_1(A_6668, '#skF_15')))), inference(resolution, [status(thm)], [c_4456, c_2382])).
% 8.70/2.79  tff(c_4538, plain, (![A_6668]: (k2_zfmisc_1(A_6668, '#skF_15')='#skF_15')), inference(resolution, [status(thm)], [c_2223, c_4494])).
% 8.70/2.79  tff(c_88, plain, (k2_zfmisc_1('#skF_14', '#skF_15')!=k1_xboole_0 | k2_zfmisc_1('#skF_16', '#skF_17')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.70/2.79  tff(c_140, plain, (k2_zfmisc_1('#skF_14', '#skF_15')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_88])).
% 8.70/2.79  tff(c_2219, plain, (k2_zfmisc_1('#skF_14', '#skF_15')!='#skF_15'), inference(demodulation, [status(thm), theory('equality')], [c_2218, c_140])).
% 8.70/2.79  tff(c_4542, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4538, c_2219])).
% 8.70/2.79  tff(c_4544, plain, (![B_6717]: (~r1_xboole_0('#skF_15', B_6717))), inference(splitRight, [status(thm)], [c_2355])).
% 8.70/2.79  tff(c_4548, plain, (![B_7]: (k3_xboole_0('#skF_15', B_7)!='#skF_15')), inference(resolution, [status(thm)], [c_2222, c_4544])).
% 8.70/2.79  tff(c_4552, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2347, c_4548])).
% 8.70/2.79  tff(c_4553, plain, (k1_xboole_0='#skF_14'), inference(splitRight, [status(thm)], [c_2216])).
% 8.70/2.79  tff(c_4561, plain, (![A_13]: (r2_hidden('#skF_3'(A_13), A_13) | A_13='#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_4553, c_16])).
% 8.70/2.79  tff(c_6896, plain, (![A_10211, B_10212, D_10213]: (r2_hidden('#skF_10'(A_10211, B_10212, k2_zfmisc_1(A_10211, B_10212), D_10213), A_10211) | ~r2_hidden(D_10213, k2_zfmisc_1(A_10211, B_10212)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.70/2.79  tff(c_4599, plain, (![A_6729, B_6730]: (k2_xboole_0(k1_tarski(A_6729), B_6730)=B_6730 | ~r2_hidden(A_6729, B_6730))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.70/2.79  tff(c_4564, plain, (![A_70, B_71]: (k2_xboole_0(k1_tarski(A_70), B_71)!='#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_4553, c_76])).
% 8.70/2.79  tff(c_4610, plain, (![A_6729]: (~r2_hidden(A_6729, '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_4599, c_4564])).
% 8.70/2.79  tff(c_4700, plain, (![C_6748, B_6749, A_6750]: (r2_hidden(C_6748, B_6749) | ~r2_hidden(C_6748, A_6750) | ~r1_tarski(A_6750, B_6749))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.70/2.79  tff(c_4851, plain, (![A_6774, B_6775]: (r2_hidden('#skF_3'(A_6774), B_6775) | ~r1_tarski(A_6774, B_6775) | A_6774='#skF_14')), inference(resolution, [status(thm)], [c_4561, c_4700])).
% 8.70/2.79  tff(c_4604, plain, (![B_6730, A_6729]: (B_6730!='#skF_14' | ~r2_hidden(A_6729, B_6730))), inference(superposition, [status(thm), theory('equality')], [c_4599, c_4564])).
% 8.70/2.79  tff(c_4887, plain, (![B_6779, A_6780]: (B_6779!='#skF_14' | ~r1_tarski(A_6780, B_6779) | A_6780='#skF_14')), inference(resolution, [status(thm)], [c_4851, c_4604])).
% 8.70/2.79  tff(c_4911, plain, (![A_6781, B_6782]: (A_6781!='#skF_14' | k3_xboole_0(A_6781, B_6782)='#skF_14')), inference(resolution, [status(thm)], [c_24, c_4887])).
% 8.70/2.79  tff(c_12, plain, (![A_8, B_9]: (r2_hidden('#skF_2'(A_8, B_9), k3_xboole_0(A_8, B_9)) | r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.70/2.79  tff(c_4926, plain, (![A_6781, B_6782]: (r2_hidden('#skF_2'(A_6781, B_6782), '#skF_14') | r1_xboole_0(A_6781, B_6782) | A_6781!='#skF_14')), inference(superposition, [status(thm), theory('equality')], [c_4911, c_12])).
% 8.70/2.79  tff(c_4941, plain, (![A_6781, B_6782]: (r1_xboole_0(A_6781, B_6782) | A_6781!='#skF_14')), inference(negUnitSimplification, [status(thm)], [c_4610, c_4926])).
% 8.70/2.79  tff(c_4929, plain, (![A_6781, B_6782, C_12]: (~r1_xboole_0(A_6781, B_6782) | ~r2_hidden(C_12, '#skF_14') | A_6781!='#skF_14')), inference(superposition, [status(thm), theory('equality')], [c_4911, c_14])).
% 8.70/2.79  tff(c_4978, plain, (![A_6789, B_6790]: (~r1_xboole_0(A_6789, B_6790) | A_6789!='#skF_14')), inference(splitLeft, [status(thm)], [c_4929])).
% 8.70/2.79  tff(c_4988, plain, (![A_6781]: (A_6781!='#skF_14')), inference(resolution, [status(thm)], [c_4941, c_4978])).
% 8.70/2.79  tff(c_4997, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4988, c_4553])).
% 8.70/2.79  tff(c_4998, plain, (![C_12]: (~r2_hidden(C_12, '#skF_14'))), inference(splitRight, [status(thm)], [c_4929])).
% 8.70/2.79  tff(c_6934, plain, (![D_10262, B_10263]: (~r2_hidden(D_10262, k2_zfmisc_1('#skF_14', B_10263)))), inference(resolution, [status(thm)], [c_6896, c_4998])).
% 8.70/2.79  tff(c_6978, plain, (![B_10263]: (k2_zfmisc_1('#skF_14', B_10263)='#skF_14')), inference(resolution, [status(thm)], [c_4561, c_6934])).
% 8.70/2.79  tff(c_4557, plain, (k2_zfmisc_1('#skF_14', '#skF_15')!='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_4553, c_140])).
% 8.70/2.79  tff(c_6982, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6978, c_4557])).
% 8.70/2.79  tff(c_6984, plain, (k2_zfmisc_1('#skF_14', '#skF_15')=k1_xboole_0), inference(splitRight, [status(thm)], [c_88])).
% 8.70/2.79  tff(c_8688, plain, (![E_12984, F_12985, A_12986, B_12987]: (r2_hidden(k4_tarski(E_12984, F_12985), k2_zfmisc_1(A_12986, B_12987)) | ~r2_hidden(F_12985, B_12987) | ~r2_hidden(E_12984, A_12986))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.70/2.79  tff(c_8698, plain, (![E_12984, F_12985]: (r2_hidden(k4_tarski(E_12984, F_12985), k1_xboole_0) | ~r2_hidden(F_12985, '#skF_15') | ~r2_hidden(E_12984, '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_6984, c_8688])).
% 8.70/2.79  tff(c_8704, plain, (![F_12985, E_12984]: (~r2_hidden(F_12985, '#skF_15') | ~r2_hidden(E_12984, '#skF_14'))), inference(negUnitSimplification, [status(thm)], [c_7063, c_8698])).
% 8.70/2.79  tff(c_8707, plain, (![E_13084]: (~r2_hidden(E_13084, '#skF_14'))), inference(splitLeft, [status(thm)], [c_8704])).
% 8.70/2.79  tff(c_8727, plain, (k1_xboole_0='#skF_14'), inference(resolution, [status(thm)], [c_16, c_8707])).
% 8.70/2.79  tff(c_8735, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8631, c_8727])).
% 8.70/2.79  tff(c_8737, plain, (![F_13133]: (~r2_hidden(F_13133, '#skF_15'))), inference(splitRight, [status(thm)], [c_8704])).
% 8.70/2.79  tff(c_8757, plain, (k1_xboole_0='#skF_15'), inference(resolution, [status(thm)], [c_16, c_8737])).
% 8.70/2.79  tff(c_8765, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8687, c_8757])).
% 8.70/2.79  tff(c_8767, plain, (k1_xboole_0='#skF_15'), inference(splitRight, [status(thm)], [c_8452])).
% 8.70/2.79  tff(c_8793, plain, ('#skF_17'!='#skF_15'), inference(demodulation, [status(thm), theory('equality')], [c_8767, c_106])).
% 8.70/2.79  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.70/2.79  tff(c_8792, plain, ('#skF_15'!='#skF_16'), inference(demodulation, [status(thm), theory('equality')], [c_8767, c_113])).
% 8.70/2.79  tff(c_8785, plain, (![C_12]: (~r2_hidden(C_12, '#skF_15'))), inference(demodulation, [status(thm), theory('equality')], [c_8767, c_7063])).
% 8.70/2.79  tff(c_6983, plain, (k2_zfmisc_1('#skF_16', '#skF_17')=k1_xboole_0), inference(splitRight, [status(thm)], [c_88])).
% 8.70/2.79  tff(c_8788, plain, (k2_zfmisc_1('#skF_16', '#skF_17')='#skF_15'), inference(demodulation, [status(thm), theory('equality')], [c_8767, c_6983])).
% 8.70/2.79  tff(c_44, plain, (![E_60, F_61, A_28, B_29]: (r2_hidden(k4_tarski(E_60, F_61), k2_zfmisc_1(A_28, B_29)) | ~r2_hidden(F_61, B_29) | ~r2_hidden(E_60, A_28))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.70/2.79  tff(c_8806, plain, (![E_60, F_61]: (r2_hidden(k4_tarski(E_60, F_61), '#skF_15') | ~r2_hidden(F_61, '#skF_17') | ~r2_hidden(E_60, '#skF_16'))), inference(superposition, [status(thm), theory('equality')], [c_8788, c_44])).
% 8.70/2.79  tff(c_8923, plain, (![F_61, E_60]: (~r2_hidden(F_61, '#skF_17') | ~r2_hidden(E_60, '#skF_16'))), inference(negUnitSimplification, [status(thm)], [c_8785, c_8806])).
% 8.70/2.79  tff(c_8925, plain, (![E_13196]: (~r2_hidden(E_13196, '#skF_16'))), inference(splitLeft, [status(thm)], [c_8923])).
% 8.70/2.79  tff(c_8945, plain, (![B_2]: (r1_tarski('#skF_16', B_2))), inference(resolution, [status(thm)], [c_6, c_8925])).
% 8.70/2.79  tff(c_7019, plain, (![A_19]: (k1_xboole_0=A_19 | ~r1_tarski(A_19, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_7007])).
% 8.70/2.79  tff(c_9061, plain, (![A_13208]: (A_13208='#skF_15' | ~r1_tarski(A_13208, '#skF_15'))), inference(demodulation, [status(thm), theory('equality')], [c_8767, c_8767, c_7019])).
% 8.70/2.79  tff(c_9065, plain, ('#skF_15'='#skF_16'), inference(resolution, [status(thm)], [c_8945, c_9061])).
% 8.70/2.79  tff(c_9089, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8792, c_9065])).
% 8.70/2.79  tff(c_9091, plain, (![F_13209]: (~r2_hidden(F_13209, '#skF_17'))), inference(splitRight, [status(thm)], [c_8923])).
% 8.70/2.79  tff(c_9111, plain, (![B_2]: (r1_tarski('#skF_17', B_2))), inference(resolution, [status(thm)], [c_6, c_9091])).
% 8.70/2.79  tff(c_9150, plain, (![A_13214]: (A_13214='#skF_15' | ~r1_tarski(A_13214, '#skF_15'))), inference(demodulation, [status(thm), theory('equality')], [c_8767, c_8767, c_7019])).
% 8.70/2.79  tff(c_9154, plain, ('#skF_17'='#skF_15'), inference(resolution, [status(thm)], [c_9111, c_9150])).
% 8.70/2.79  tff(c_9178, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8793, c_9154])).
% 8.70/2.79  tff(c_9180, plain, (k1_xboole_0='#skF_14'), inference(splitRight, [status(thm)], [c_8250])).
% 8.70/2.79  tff(c_9260, plain, ('#skF_17'!='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_9180, c_106])).
% 8.70/2.79  tff(c_9259, plain, ('#skF_16'!='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_9180, c_113])).
% 8.70/2.79  tff(c_9252, plain, (![C_12]: (~r2_hidden(C_12, '#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_9180, c_7063])).
% 8.70/2.79  tff(c_9255, plain, (k2_zfmisc_1('#skF_16', '#skF_17')='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_9180, c_6983])).
% 8.70/2.79  tff(c_9306, plain, (![E_13270, F_13271, A_13272, B_13273]: (r2_hidden(k4_tarski(E_13270, F_13271), k2_zfmisc_1(A_13272, B_13273)) | ~r2_hidden(F_13271, B_13273) | ~r2_hidden(E_13270, A_13272))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.70/2.79  tff(c_9311, plain, (![E_13270, F_13271]: (r2_hidden(k4_tarski(E_13270, F_13271), '#skF_14') | ~r2_hidden(F_13271, '#skF_17') | ~r2_hidden(E_13270, '#skF_16'))), inference(superposition, [status(thm), theory('equality')], [c_9255, c_9306])).
% 8.70/2.79  tff(c_9316, plain, (![F_13271, E_13270]: (~r2_hidden(F_13271, '#skF_17') | ~r2_hidden(E_13270, '#skF_16'))), inference(negUnitSimplification, [status(thm)], [c_9252, c_9311])).
% 8.70/2.79  tff(c_9360, plain, (![E_13276]: (~r2_hidden(E_13276, '#skF_16'))), inference(splitLeft, [status(thm)], [c_9316])).
% 8.70/2.79  tff(c_9375, plain, (![B_2]: (r1_tarski('#skF_16', B_2))), inference(resolution, [status(thm)], [c_6, c_9360])).
% 8.70/2.79  tff(c_9486, plain, (![A_13288]: (A_13288='#skF_14' | ~r1_tarski(A_13288, '#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_9180, c_9180, c_7019])).
% 8.70/2.79  tff(c_9490, plain, ('#skF_16'='#skF_14'), inference(resolution, [status(thm)], [c_9375, c_9486])).
% 8.70/2.79  tff(c_9514, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9259, c_9490])).
% 8.70/2.79  tff(c_9516, plain, (![F_13289]: (~r2_hidden(F_13289, '#skF_17'))), inference(splitRight, [status(thm)], [c_9316])).
% 8.70/2.79  tff(c_9531, plain, (![B_2]: (r1_tarski('#skF_17', B_2))), inference(resolution, [status(thm)], [c_6, c_9516])).
% 8.70/2.79  tff(c_9637, plain, (![A_13299]: (A_13299='#skF_14' | ~r1_tarski(A_13299, '#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_9180, c_9180, c_7019])).
% 8.70/2.79  tff(c_9641, plain, ('#skF_17'='#skF_14'), inference(resolution, [status(thm)], [c_9531, c_9637])).
% 8.70/2.79  tff(c_9665, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9260, c_9641])).
% 8.70/2.79  tff(c_9667, plain, (![B_13300]: (~r1_xboole_0(k1_xboole_0, B_13300))), inference(splitRight, [status(thm)], [c_7054])).
% 8.70/2.79  tff(c_9671, plain, (![B_7]: (k3_xboole_0(k1_xboole_0, B_7)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_9667])).
% 8.70/2.79  tff(c_9675, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7033, c_9671])).
% 8.70/2.79  tff(c_9677, plain, (k1_xboole_0='#skF_16'), inference(splitRight, [status(thm)], [c_86])).
% 8.70/2.79  tff(c_9680, plain, (![A_19]: (r1_tarski('#skF_16', A_19))), inference(demodulation, [status(thm), theory('equality')], [c_9677, c_26])).
% 8.70/2.79  tff(c_9750, plain, (![B_13317, A_13318]: (B_13317=A_13318 | ~r1_tarski(B_13317, A_13318) | ~r1_tarski(A_13318, B_13317))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.70/2.79  tff(c_9777, plain, (![A_13320]: (A_13320='#skF_16' | ~r1_tarski(A_13320, '#skF_16'))), inference(resolution, [status(thm)], [c_9680, c_9750])).
% 8.70/2.79  tff(c_9792, plain, (![B_18]: (k3_xboole_0('#skF_16', B_18)='#skF_16')), inference(resolution, [status(thm)], [c_24, c_9777])).
% 8.70/2.79  tff(c_9703, plain, (![A_6, B_7]: (r1_xboole_0(A_6, B_7) | k3_xboole_0(A_6, B_7)!='#skF_16')), inference(demodulation, [status(thm), theory('equality')], [c_9677, c_10])).
% 8.70/2.79  tff(c_9696, plain, (![A_13]: (r2_hidden('#skF_3'(A_13), A_13) | A_13='#skF_16')), inference(demodulation, [status(thm), theory('equality')], [c_9677, c_16])).
% 8.70/2.80  tff(c_12150, plain, (![A_16792, B_16793, D_16794]: (r2_hidden('#skF_11'(A_16792, B_16793, k2_zfmisc_1(A_16792, B_16793), D_16794), B_16793) | ~r2_hidden(D_16794, k2_zfmisc_1(A_16792, B_16793)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.70/2.80  tff(c_9828, plain, (![A_13326, B_13327, C_13328]: (~r1_xboole_0(A_13326, B_13327) | ~r2_hidden(C_13328, k3_xboole_0(A_13326, B_13327)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.70/2.80  tff(c_9831, plain, (![B_18, C_13328]: (~r1_xboole_0('#skF_16', B_18) | ~r2_hidden(C_13328, '#skF_16'))), inference(superposition, [status(thm), theory('equality')], [c_9792, c_9828])).
% 8.70/2.80  tff(c_9837, plain, (![C_13328]: (~r2_hidden(C_13328, '#skF_16'))), inference(splitLeft, [status(thm)], [c_9831])).
% 8.70/2.80  tff(c_12188, plain, (![D_16843, A_16844]: (~r2_hidden(D_16843, k2_zfmisc_1(A_16844, '#skF_16')))), inference(resolution, [status(thm)], [c_12150, c_9837])).
% 8.70/2.80  tff(c_12232, plain, (![A_16844]: (k2_zfmisc_1(A_16844, '#skF_16')='#skF_16')), inference(resolution, [status(thm)], [c_9696, c_12188])).
% 8.70/2.80  tff(c_9676, plain, (k1_xboole_0='#skF_14' | k1_xboole_0='#skF_15'), inference(splitRight, [status(thm)], [c_86])).
% 8.70/2.80  tff(c_9688, plain, ('#skF_16'='#skF_14' | '#skF_15'='#skF_16'), inference(demodulation, [status(thm), theory('equality')], [c_9677, c_9677, c_9676])).
% 8.70/2.80  tff(c_9689, plain, ('#skF_15'='#skF_16'), inference(splitLeft, [status(thm)], [c_9688])).
% 8.70/2.80  tff(c_84, plain, (k2_zfmisc_1('#skF_14', '#skF_15')!=k1_xboole_0 | k1_xboole_0!='#skF_16'), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.70/2.80  tff(c_9686, plain, (k2_zfmisc_1('#skF_14', '#skF_15')!='#skF_16'), inference(demodulation, [status(thm), theory('equality')], [c_9677, c_9677, c_84])).
% 8.70/2.80  tff(c_9690, plain, (k2_zfmisc_1('#skF_14', '#skF_16')!='#skF_16'), inference(demodulation, [status(thm), theory('equality')], [c_9689, c_9686])).
% 8.70/2.80  tff(c_12236, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12232, c_9690])).
% 8.70/2.80  tff(c_12238, plain, (![B_16893]: (~r1_xboole_0('#skF_16', B_16893))), inference(splitRight, [status(thm)], [c_9831])).
% 8.70/2.80  tff(c_12242, plain, (![B_7]: (k3_xboole_0('#skF_16', B_7)!='#skF_16')), inference(resolution, [status(thm)], [c_9703, c_12238])).
% 8.70/2.80  tff(c_12246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9792, c_12242])).
% 8.70/2.80  tff(c_12247, plain, ('#skF_16'='#skF_14'), inference(splitRight, [status(thm)], [c_9688])).
% 8.70/2.80  tff(c_12253, plain, (k1_xboole_0='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_12247, c_9677])).
% 8.70/2.80  tff(c_12266, plain, (![A_13]: (r2_hidden('#skF_3'(A_13), A_13) | A_13='#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_12253, c_16])).
% 8.70/2.80  tff(c_14411, plain, (![A_20083, B_20084, D_20085]: (r2_hidden('#skF_10'(A_20083, B_20084, k2_zfmisc_1(A_20083, B_20084), D_20085), A_20083) | ~r2_hidden(D_20085, k2_zfmisc_1(A_20083, B_20084)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.70/2.80  tff(c_12297, plain, (![A_16903, B_16904]: (k2_xboole_0(k1_tarski(A_16903), B_16904)=B_16904 | ~r2_hidden(A_16903, B_16904))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.70/2.80  tff(c_9679, plain, (![A_70, B_71]: (k2_xboole_0(k1_tarski(A_70), B_71)!='#skF_16')), inference(demodulation, [status(thm), theory('equality')], [c_9677, c_76])).
% 8.70/2.80  tff(c_12264, plain, (![A_70, B_71]: (k2_xboole_0(k1_tarski(A_70), B_71)!='#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_12247, c_9679])).
% 8.70/2.80  tff(c_12308, plain, (![A_16903]: (~r2_hidden(A_16903, '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_12297, c_12264])).
% 8.70/2.80  tff(c_12419, plain, (![C_16928, B_16929, A_16930]: (r2_hidden(C_16928, B_16929) | ~r2_hidden(C_16928, A_16930) | ~r1_tarski(A_16930, B_16929))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.70/2.80  tff(c_12550, plain, (![A_16950, B_16951]: (r2_hidden('#skF_3'(A_16950), B_16951) | ~r1_tarski(A_16950, B_16951) | A_16950='#skF_14')), inference(resolution, [status(thm)], [c_12266, c_12419])).
% 8.70/2.80  tff(c_12302, plain, (![B_16904, A_16903]: (B_16904!='#skF_14' | ~r2_hidden(A_16903, B_16904))), inference(superposition, [status(thm), theory('equality')], [c_12297, c_12264])).
% 8.70/2.80  tff(c_12578, plain, (![B_16952, A_16953]: (B_16952!='#skF_14' | ~r1_tarski(A_16953, B_16952) | A_16953='#skF_14')), inference(resolution, [status(thm)], [c_12550, c_12302])).
% 8.70/2.80  tff(c_12602, plain, (![A_16954, B_16955]: (A_16954!='#skF_14' | k3_xboole_0(A_16954, B_16955)='#skF_14')), inference(resolution, [status(thm)], [c_24, c_12578])).
% 8.70/2.80  tff(c_12611, plain, (![A_16954, B_16955]: (r2_hidden('#skF_2'(A_16954, B_16955), '#skF_14') | r1_xboole_0(A_16954, B_16955) | A_16954!='#skF_14')), inference(superposition, [status(thm), theory('equality')], [c_12602, c_12])).
% 8.70/2.80  tff(c_12631, plain, (![A_16954, B_16955]: (r1_xboole_0(A_16954, B_16955) | A_16954!='#skF_14')), inference(negUnitSimplification, [status(thm)], [c_12308, c_12611])).
% 8.70/2.80  tff(c_12620, plain, (![A_16954, B_16955, C_12]: (~r1_xboole_0(A_16954, B_16955) | ~r2_hidden(C_12, '#skF_14') | A_16954!='#skF_14')), inference(superposition, [status(thm), theory('equality')], [c_12602, c_14])).
% 8.70/2.80  tff(c_12676, plain, (![A_16963, B_16964]: (~r1_xboole_0(A_16963, B_16964) | A_16963!='#skF_14')), inference(splitLeft, [status(thm)], [c_12620])).
% 8.70/2.80  tff(c_12686, plain, (![A_16954]: (A_16954!='#skF_14')), inference(resolution, [status(thm)], [c_12631, c_12676])).
% 8.70/2.80  tff(c_12696, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12686, c_12253])).
% 8.70/2.80  tff(c_12697, plain, (![C_12]: (~r2_hidden(C_12, '#skF_14'))), inference(splitRight, [status(thm)], [c_12620])).
% 8.70/2.80  tff(c_14441, plain, (![D_20134, B_20135]: (~r2_hidden(D_20134, k2_zfmisc_1('#skF_14', B_20135)))), inference(resolution, [status(thm)], [c_14411, c_12697])).
% 8.70/2.80  tff(c_14477, plain, (![B_20135]: (k2_zfmisc_1('#skF_14', B_20135)='#skF_14')), inference(resolution, [status(thm)], [c_12266, c_14441])).
% 8.70/2.80  tff(c_12252, plain, (k2_zfmisc_1('#skF_14', '#skF_15')!='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_12247, c_9686])).
% 8.70/2.80  tff(c_14481, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14477, c_12252])).
% 8.70/2.80  tff(c_14483, plain, (k1_xboole_0='#skF_17'), inference(splitRight, [status(thm)], [c_80])).
% 8.70/2.80  tff(c_82, plain, (k1_xboole_0='#skF_15' | k1_xboole_0='#skF_14' | k1_xboole_0!='#skF_17'), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.70/2.80  tff(c_14499, plain, ('#skF_17'='#skF_15' | '#skF_17'='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_14483, c_14483, c_14483, c_82])).
% 8.70/2.80  tff(c_14500, plain, ('#skF_17'='#skF_14'), inference(splitLeft, [status(thm)], [c_14499])).
% 8.70/2.80  tff(c_14496, plain, (![A_13]: (r2_hidden('#skF_3'(A_13), A_13) | A_13='#skF_17')), inference(demodulation, [status(thm), theory('equality')], [c_14483, c_16])).
% 8.70/2.80  tff(c_14501, plain, (![A_13]: (r2_hidden('#skF_3'(A_13), A_13) | A_13='#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_14500, c_14496])).
% 8.70/2.80  tff(c_16746, plain, (![A_23426, B_23427, D_23428]: (r2_hidden('#skF_10'(A_23426, B_23427, k2_zfmisc_1(A_23426, B_23427), D_23428), A_23426) | ~r2_hidden(D_23428, k2_zfmisc_1(A_23426, B_23427)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.70/2.80  tff(c_14560, plain, (![A_20201, B_20202]: (k2_xboole_0(k1_tarski(A_20201), B_20202)=B_20202 | ~r2_hidden(A_20201, B_20202))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.70/2.80  tff(c_14484, plain, (![A_70, B_71]: (k2_xboole_0(k1_tarski(A_70), B_71)!='#skF_17')), inference(demodulation, [status(thm), theory('equality')], [c_14483, c_76])).
% 8.70/2.80  tff(c_14502, plain, (![A_70, B_71]: (k2_xboole_0(k1_tarski(A_70), B_71)!='#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_14500, c_14484])).
% 8.70/2.80  tff(c_14571, plain, (![A_20201]: (~r2_hidden(A_20201, '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_14560, c_14502])).
% 8.70/2.80  tff(c_14691, plain, (![C_20226, B_20227, A_20228]: (r2_hidden(C_20226, B_20227) | ~r2_hidden(C_20226, A_20228) | ~r1_tarski(A_20228, B_20227))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.70/2.80  tff(c_14806, plain, (![A_20244, B_20245]: (r2_hidden('#skF_3'(A_20244), B_20245) | ~r1_tarski(A_20244, B_20245) | A_20244='#skF_14')), inference(resolution, [status(thm)], [c_14501, c_14691])).
% 8.70/2.80  tff(c_14565, plain, (![B_20202, A_20201]: (B_20202!='#skF_14' | ~r2_hidden(A_20201, B_20202))), inference(superposition, [status(thm), theory('equality')], [c_14560, c_14502])).
% 8.70/2.80  tff(c_14842, plain, (![B_20249, A_20250]: (B_20249!='#skF_14' | ~r1_tarski(A_20250, B_20249) | A_20250='#skF_14')), inference(resolution, [status(thm)], [c_14806, c_14565])).
% 8.70/2.80  tff(c_14866, plain, (![A_20251, B_20252]: (A_20251!='#skF_14' | k3_xboole_0(A_20251, B_20252)='#skF_14')), inference(resolution, [status(thm)], [c_24, c_14842])).
% 8.70/2.80  tff(c_14875, plain, (![A_20251, B_20252]: (r2_hidden('#skF_2'(A_20251, B_20252), '#skF_14') | r1_xboole_0(A_20251, B_20252) | A_20251!='#skF_14')), inference(superposition, [status(thm), theory('equality')], [c_14866, c_12])).
% 8.70/2.80  tff(c_14895, plain, (![A_20251, B_20252]: (r1_xboole_0(A_20251, B_20252) | A_20251!='#skF_14')), inference(negUnitSimplification, [status(thm)], [c_14571, c_14875])).
% 8.70/2.80  tff(c_14884, plain, (![A_20251, B_20252, C_12]: (~r1_xboole_0(A_20251, B_20252) | ~r2_hidden(C_12, '#skF_14') | A_20251!='#skF_14')), inference(superposition, [status(thm), theory('equality')], [c_14866, c_14])).
% 8.70/2.80  tff(c_14933, plain, (![A_20259, B_20260]: (~r1_xboole_0(A_20259, B_20260) | A_20259!='#skF_14')), inference(splitLeft, [status(thm)], [c_14884])).
% 8.70/2.80  tff(c_14943, plain, (![A_20251]: (A_20251!='#skF_14')), inference(resolution, [status(thm)], [c_14895, c_14933])).
% 8.70/2.80  tff(c_14506, plain, (k1_xboole_0='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_14500, c_14483])).
% 8.70/2.80  tff(c_14953, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14943, c_14506])).
% 8.70/2.80  tff(c_14954, plain, (![C_12]: (~r2_hidden(C_12, '#skF_14'))), inference(splitRight, [status(thm)], [c_14884])).
% 8.70/2.80  tff(c_16780, plain, (![D_23477, B_23478]: (~r2_hidden(D_23477, k2_zfmisc_1('#skF_14', B_23478)))), inference(resolution, [status(thm)], [c_16746, c_14954])).
% 8.70/2.80  tff(c_16824, plain, (![B_23478]: (k2_zfmisc_1('#skF_14', B_23478)='#skF_14')), inference(resolution, [status(thm)], [c_14501, c_16780])).
% 8.70/2.80  tff(c_14482, plain, (k2_zfmisc_1('#skF_14', '#skF_15')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_80])).
% 8.70/2.80  tff(c_14493, plain, (k2_zfmisc_1('#skF_14', '#skF_15')!='#skF_17'), inference(demodulation, [status(thm), theory('equality')], [c_14483, c_14482])).
% 8.70/2.80  tff(c_14503, plain, (k2_zfmisc_1('#skF_14', '#skF_15')!='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_14500, c_14493])).
% 8.70/2.80  tff(c_16828, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16824, c_14503])).
% 8.70/2.80  tff(c_16829, plain, ('#skF_17'='#skF_15'), inference(splitRight, [status(thm)], [c_14499])).
% 8.70/2.80  tff(c_16831, plain, (![A_13]: (r2_hidden('#skF_3'(A_13), A_13) | A_13='#skF_15')), inference(demodulation, [status(thm), theory('equality')], [c_16829, c_14496])).
% 8.70/2.80  tff(c_19121, plain, (![A_26824, B_26825, D_26826]: (r2_hidden('#skF_11'(A_26824, B_26825, k2_zfmisc_1(A_26824, B_26825), D_26826), B_26825) | ~r2_hidden(D_26826, k2_zfmisc_1(A_26824, B_26825)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.70/2.80  tff(c_16916, plain, (![A_23546, B_23547]: (k2_xboole_0(k1_tarski(A_23546), B_23547)=B_23547 | ~r2_hidden(A_23546, B_23547))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.70/2.80  tff(c_16832, plain, (![A_70, B_71]: (k2_xboole_0(k1_tarski(A_70), B_71)!='#skF_15')), inference(demodulation, [status(thm), theory('equality')], [c_16829, c_14484])).
% 8.70/2.80  tff(c_16934, plain, (![A_23546]: (~r2_hidden(A_23546, '#skF_15'))), inference(superposition, [status(thm), theory('equality')], [c_16916, c_16832])).
% 8.70/2.80  tff(c_17007, plain, (![C_23563, B_23564, A_23565]: (r2_hidden(C_23563, B_23564) | ~r2_hidden(C_23563, A_23565) | ~r1_tarski(A_23565, B_23564))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.70/2.80  tff(c_17119, plain, (![A_23581, B_23582]: (r2_hidden('#skF_3'(A_23581), B_23582) | ~r1_tarski(A_23581, B_23582) | A_23581='#skF_15')), inference(resolution, [status(thm)], [c_16831, c_17007])).
% 8.70/2.80  tff(c_16925, plain, (![B_23547, A_23546]: (B_23547!='#skF_15' | ~r2_hidden(A_23546, B_23547))), inference(superposition, [status(thm), theory('equality')], [c_16916, c_16832])).
% 8.70/2.80  tff(c_17142, plain, (![B_23583, A_23584]: (B_23583!='#skF_15' | ~r1_tarski(A_23584, B_23583) | A_23584='#skF_15')), inference(resolution, [status(thm)], [c_17119, c_16925])).
% 8.70/2.80  tff(c_17174, plain, (![A_23588, B_23589]: (A_23588!='#skF_15' | k3_xboole_0(A_23588, B_23589)='#skF_15')), inference(resolution, [status(thm)], [c_24, c_17142])).
% 8.70/2.80  tff(c_17183, plain, (![A_23588, B_23589]: (r2_hidden('#skF_2'(A_23588, B_23589), '#skF_15') | r1_xboole_0(A_23588, B_23589) | A_23588!='#skF_15')), inference(superposition, [status(thm), theory('equality')], [c_17174, c_12])).
% 8.70/2.80  tff(c_17203, plain, (![A_23588, B_23589]: (r1_xboole_0(A_23588, B_23589) | A_23588!='#skF_15')), inference(negUnitSimplification, [status(thm)], [c_16934, c_17183])).
% 8.70/2.80  tff(c_17192, plain, (![A_23588, B_23589, C_12]: (~r1_xboole_0(A_23588, B_23589) | ~r2_hidden(C_12, '#skF_15') | A_23588!='#skF_15')), inference(superposition, [status(thm), theory('equality')], [c_17174, c_14])).
% 8.70/2.80  tff(c_17240, plain, (![A_23594, B_23595]: (~r1_xboole_0(A_23594, B_23595) | A_23594!='#skF_15')), inference(splitLeft, [status(thm)], [c_17192])).
% 8.70/2.80  tff(c_17250, plain, (![A_23588]: (A_23588!='#skF_15')), inference(resolution, [status(thm)], [c_17203, c_17240])).
% 8.70/2.80  tff(c_16836, plain, (k1_xboole_0='#skF_15'), inference(demodulation, [status(thm), theory('equality')], [c_16829, c_14483])).
% 8.70/2.80  tff(c_17261, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17250, c_16836])).
% 8.70/2.80  tff(c_17262, plain, (![C_12]: (~r2_hidden(C_12, '#skF_15'))), inference(splitRight, [status(thm)], [c_17192])).
% 8.70/2.80  tff(c_19151, plain, (![D_26875, A_26876]: (~r2_hidden(D_26875, k2_zfmisc_1(A_26876, '#skF_15')))), inference(resolution, [status(thm)], [c_19121, c_17262])).
% 8.70/2.80  tff(c_19192, plain, (![A_26876]: (k2_zfmisc_1(A_26876, '#skF_15')='#skF_15')), inference(resolution, [status(thm)], [c_16831, c_19151])).
% 8.70/2.80  tff(c_16833, plain, (k2_zfmisc_1('#skF_14', '#skF_15')!='#skF_15'), inference(demodulation, [status(thm), theory('equality')], [c_16829, c_14493])).
% 8.70/2.80  tff(c_19196, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19192, c_16833])).
% 8.70/2.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.70/2.80  
% 8.70/2.80  Inference rules
% 8.70/2.80  ----------------------
% 8.70/2.80  #Ref     : 15
% 8.70/2.80  #Sup     : 2585
% 8.70/2.80  #Fact    : 0
% 8.70/2.80  #Define  : 0
% 8.70/2.80  #Split   : 28
% 8.70/2.80  #Chain   : 0
% 8.70/2.80  #Close   : 0
% 8.70/2.80  
% 8.70/2.80  Ordering : KBO
% 8.70/2.80  
% 8.70/2.80  Simplification rules
% 8.70/2.80  ----------------------
% 8.70/2.80  #Subsume      : 867
% 8.70/2.80  #Demod        : 1303
% 8.70/2.80  #Tautology    : 1057
% 8.70/2.80  #SimpNegUnit  : 227
% 8.70/2.80  #BackRed      : 138
% 8.70/2.80  
% 8.70/2.80  #Partial instantiations: 12864
% 8.70/2.80  #Strategies tried      : 1
% 8.70/2.80  
% 8.70/2.80  Timing (in seconds)
% 8.70/2.80  ----------------------
% 8.70/2.80  Preprocessing        : 0.35
% 8.70/2.80  Parsing              : 0.18
% 8.70/2.80  CNF conversion       : 0.03
% 8.70/2.80  Main loop            : 1.65
% 8.70/2.80  Inferencing          : 0.83
% 8.70/2.80  Reduction            : 0.41
% 8.70/2.80  Demodulation         : 0.27
% 8.70/2.80  BG Simplification    : 0.05
% 8.70/2.80  Subsumption          : 0.25
% 8.70/2.80  Abstraction          : 0.07
% 8.70/2.80  MUC search           : 0.00
% 8.70/2.80  Cooper               : 0.00
% 8.70/2.80  Total                : 2.08
% 8.70/2.80  Index Insertion      : 0.00
% 8.70/2.80  Index Deletion       : 0.00
% 8.70/2.80  Index Matching       : 0.00
% 8.70/2.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
