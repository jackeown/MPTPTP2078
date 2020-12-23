%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:01 EST 2020

% Result     : Theorem 22.69s
% Output     : CNFRefutation 22.75s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 244 expanded)
%              Number of leaves         :   36 (  96 expanded)
%              Depth                    :   12
%              Number of atoms          :  188 ( 763 expanded)
%              Number of equality atoms :   21 (  91 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_enumset1 > k3_enumset1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_11 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_2 > #skF_12 > #skF_4

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

tff('#skF_6',type,(
    '#skF_6': $i )).

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
    '#skF_5': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_138,negated_conjecture,(
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
                           => ( A != k1_xboole_0
                             => m1_subset_1(k4_enumset1(B,C,D,E,F,G),k1_zfmisc_1(A)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_subset_1)).

tff(f_115,axiom,(
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

tff(f_89,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_86,axiom,(
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

tff(f_96,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_80,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_90,plain,(
    m1_subset_1('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_88,plain,(
    m1_subset_1('#skF_9','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_86,plain,(
    m1_subset_1('#skF_10','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_84,plain,(
    m1_subset_1('#skF_11','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_82,plain,(
    m1_subset_1('#skF_12','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1702,plain,(
    ! [C_482,E_479,B_481,D_478,F_477,A_480] :
      ( m1_subset_1(k3_enumset1(B_481,C_482,D_478,E_479,F_477),k1_zfmisc_1(A_480))
      | k1_xboole_0 = A_480
      | ~ m1_subset_1(F_477,A_480)
      | ~ m1_subset_1(E_479,A_480)
      | ~ m1_subset_1(D_478,A_480)
      | ~ m1_subset_1(C_482,A_480)
      | ~ m1_subset_1(B_481,A_480) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_72,plain,(
    ! [A_38] : ~ v1_xboole_0(k1_zfmisc_1(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_181,plain,(
    ! [B_174,A_175] :
      ( r2_hidden(B_174,A_175)
      | ~ m1_subset_1(B_174,A_175)
      | v1_xboole_0(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_12,plain,(
    ! [C_24,A_20] :
      ( r1_tarski(C_24,A_20)
      | ~ r2_hidden(C_24,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_185,plain,(
    ! [B_174,A_20] :
      ( r1_tarski(B_174,A_20)
      | ~ m1_subset_1(B_174,k1_zfmisc_1(A_20))
      | v1_xboole_0(k1_zfmisc_1(A_20)) ) ),
    inference(resolution,[status(thm)],[c_181,c_12])).

tff(c_191,plain,(
    ! [B_174,A_20] :
      ( r1_tarski(B_174,A_20)
      | ~ m1_subset_1(B_174,k1_zfmisc_1(A_20)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_185])).

tff(c_26803,plain,(
    ! [A_1422,C_1420,D_1421,B_1419,F_1418,E_1417] :
      ( r1_tarski(k3_enumset1(B_1419,C_1420,D_1421,E_1417,F_1418),A_1422)
      | k1_xboole_0 = A_1422
      | ~ m1_subset_1(F_1418,A_1422)
      | ~ m1_subset_1(E_1417,A_1422)
      | ~ m1_subset_1(D_1421,A_1422)
      | ~ m1_subset_1(C_1420,A_1422)
      | ~ m1_subset_1(B_1419,A_1422) ) ),
    inference(resolution,[status(thm)],[c_1702,c_191])).

tff(c_129,plain,(
    ! [B_147,A_148] :
      ( v1_xboole_0(B_147)
      | ~ m1_subset_1(B_147,A_148)
      | ~ v1_xboole_0(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_152,plain,
    ( v1_xboole_0('#skF_12')
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_129])).

tff(c_158,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_152])).

tff(c_92,plain,(
    m1_subset_1('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_30,plain,(
    ! [B_28,A_27] :
      ( r2_hidden(B_28,A_27)
      | ~ m1_subset_1(B_28,A_27)
      | v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_26,plain,(
    ! [A_25,B_26] :
      ( r1_tarski(k1_tarski(A_25),B_26)
      | ~ r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_578,plain,(
    ! [B_278,D_280,A_276,C_279,E_277,F_275] : k2_xboole_0(k1_tarski(A_276),k3_enumset1(B_278,C_279,D_280,E_277,F_275)) = k4_enumset1(A_276,B_278,C_279,D_280,E_277,F_275) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(k2_xboole_0(A_5,C_7),B_6)
      | ~ r1_tarski(C_7,B_6)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5779,plain,(
    ! [F_785,A_789,B_788,E_786,D_787,B_790,C_791] :
      ( r1_tarski(k4_enumset1(A_789,B_790,C_791,D_787,E_786,F_785),B_788)
      | ~ r1_tarski(k3_enumset1(B_790,C_791,D_787,E_786,F_785),B_788)
      | ~ r1_tarski(k1_tarski(A_789),B_788) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_578,c_6])).

tff(c_14,plain,(
    ! [C_24,A_20] :
      ( r2_hidden(C_24,k1_zfmisc_1(A_20))
      | ~ r1_tarski(C_24,A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_199,plain,(
    ! [B_178,A_179] :
      ( m1_subset_1(B_178,A_179)
      | ~ r2_hidden(B_178,A_179)
      | v1_xboole_0(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_217,plain,(
    ! [C_24,A_20] :
      ( m1_subset_1(C_24,k1_zfmisc_1(A_20))
      | v1_xboole_0(k1_zfmisc_1(A_20))
      | ~ r1_tarski(C_24,A_20) ) ),
    inference(resolution,[status(thm)],[c_14,c_199])).

tff(c_261,plain,(
    ! [C_186,A_187] :
      ( m1_subset_1(C_186,k1_zfmisc_1(A_187))
      | ~ r1_tarski(C_186,A_187) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_217])).

tff(c_78,plain,(
    ~ m1_subset_1(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_273,plain,(
    ~ r1_tarski(k4_enumset1('#skF_7','#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_261,c_78])).

tff(c_5845,plain,
    ( ~ r1_tarski(k3_enumset1('#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6')
    | ~ r1_tarski(k1_tarski('#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_5779,c_273])).

tff(c_5846,plain,(
    ~ r1_tarski(k1_tarski('#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_5845])).

tff(c_5850,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_5846])).

tff(c_5856,plain,
    ( ~ m1_subset_1('#skF_7','#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_30,c_5850])).

tff(c_5860,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_5856])).

tff(c_5862,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_158,c_5860])).

tff(c_5863,plain,(
    ~ r1_tarski(k3_enumset1('#skF_8','#skF_9','#skF_10','#skF_11','#skF_12'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_5845])).

tff(c_26897,plain,
    ( k1_xboole_0 = '#skF_6'
    | ~ m1_subset_1('#skF_12','#skF_6')
    | ~ m1_subset_1('#skF_11','#skF_6')
    | ~ m1_subset_1('#skF_10','#skF_6')
    | ~ m1_subset_1('#skF_9','#skF_6')
    | ~ m1_subset_1('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_26803,c_5863])).

tff(c_27023,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_84,c_82,c_26897])).

tff(c_27025,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_27023])).

tff(c_27027,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_27038,plain,(
    ! [G_1427,D_1423,B_1424,E_1426,A_1425] : r2_hidden(G_1427,k3_enumset1(A_1425,B_1424,G_1427,D_1423,E_1426)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_27042,plain,(
    ! [G_1427,D_1423,B_1424,E_1426,A_1425] : ~ v1_xboole_0(k3_enumset1(A_1425,B_1424,G_1427,D_1423,E_1426)) ),
    inference(resolution,[status(thm)],[c_27038,c_2])).

tff(c_28219,plain,(
    ! [C_1702,B_1701,E_1699,F_1697,D_1698,A_1700] :
      ( m1_subset_1(k3_enumset1(B_1701,C_1702,D_1698,E_1699,F_1697),k1_zfmisc_1(A_1700))
      | k1_xboole_0 = A_1700
      | ~ m1_subset_1(F_1697,A_1700)
      | ~ m1_subset_1(E_1699,A_1700)
      | ~ m1_subset_1(D_1698,A_1700)
      | ~ m1_subset_1(C_1702,A_1700)
      | ~ m1_subset_1(B_1701,A_1700) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_27152,plain,(
    ! [C_1462,A_1463,B_1464] :
      ( r2_hidden(C_1462,A_1463)
      | ~ r2_hidden(C_1462,B_1464)
      | ~ m1_subset_1(B_1464,k1_zfmisc_1(A_1463)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_27203,plain,(
    ! [A_1493,A_1494] :
      ( r2_hidden('#skF_1'(A_1493),A_1494)
      | ~ m1_subset_1(A_1493,k1_zfmisc_1(A_1494))
      | v1_xboole_0(A_1493) ) ),
    inference(resolution,[status(thm)],[c_4,c_27152])).

tff(c_27219,plain,(
    ! [A_1494,A_1493] :
      ( ~ v1_xboole_0(A_1494)
      | ~ m1_subset_1(A_1493,k1_zfmisc_1(A_1494))
      | v1_xboole_0(A_1493) ) ),
    inference(resolution,[status(thm)],[c_27203,c_2])).

tff(c_28253,plain,(
    ! [C_1702,B_1701,E_1699,F_1697,D_1698,A_1700] :
      ( ~ v1_xboole_0(A_1700)
      | v1_xboole_0(k3_enumset1(B_1701,C_1702,D_1698,E_1699,F_1697))
      | k1_xboole_0 = A_1700
      | ~ m1_subset_1(F_1697,A_1700)
      | ~ m1_subset_1(E_1699,A_1700)
      | ~ m1_subset_1(D_1698,A_1700)
      | ~ m1_subset_1(C_1702,A_1700)
      | ~ m1_subset_1(B_1701,A_1700) ) ),
    inference(resolution,[status(thm)],[c_28219,c_27219])).

tff(c_48187,plain,(
    ! [F_2471,E_2472,B_2467,D_2468,A_2469,C_2470] :
      ( ~ v1_xboole_0(A_2469)
      | k1_xboole_0 = A_2469
      | ~ m1_subset_1(F_2471,A_2469)
      | ~ m1_subset_1(E_2472,A_2469)
      | ~ m1_subset_1(D_2468,A_2469)
      | ~ m1_subset_1(C_2470,A_2469)
      | ~ m1_subset_1(B_2467,A_2469) ) ),
    inference(negUnitSimplification,[status(thm)],[c_27042,c_28253])).

tff(c_48247,plain,(
    ! [E_2472,D_2468,C_2470,B_2467] :
      ( ~ v1_xboole_0('#skF_6')
      | k1_xboole_0 = '#skF_6'
      | ~ m1_subset_1(E_2472,'#skF_6')
      | ~ m1_subset_1(D_2468,'#skF_6')
      | ~ m1_subset_1(C_2470,'#skF_6')
      | ~ m1_subset_1(B_2467,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_82,c_48187])).

tff(c_48291,plain,(
    ! [E_2472,D_2468,C_2470,B_2467] :
      ( k1_xboole_0 = '#skF_6'
      | ~ m1_subset_1(E_2472,'#skF_6')
      | ~ m1_subset_1(D_2468,'#skF_6')
      | ~ m1_subset_1(C_2470,'#skF_6')
      | ~ m1_subset_1(B_2467,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27027,c_48247])).

tff(c_48292,plain,(
    ! [E_2472,D_2468,C_2470,B_2467] :
      ( ~ m1_subset_1(E_2472,'#skF_6')
      | ~ m1_subset_1(D_2468,'#skF_6')
      | ~ m1_subset_1(C_2470,'#skF_6')
      | ~ m1_subset_1(B_2467,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_48291])).

tff(c_48313,plain,(
    ! [B_2467] : ~ m1_subset_1(B_2467,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_48292])).

tff(c_48320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48313,c_82])).

tff(c_48321,plain,(
    ! [D_2468,E_2472,C_2470] :
      ( ~ m1_subset_1(D_2468,'#skF_6')
      | ~ m1_subset_1(E_2472,'#skF_6')
      | ~ m1_subset_1(C_2470,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_48292])).

tff(c_48440,plain,(
    ! [C_2470] : ~ m1_subset_1(C_2470,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_48321])).

tff(c_48447,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48440,c_82])).

tff(c_48448,plain,(
    ! [D_2468,E_2472] :
      ( ~ m1_subset_1(D_2468,'#skF_6')
      | ~ m1_subset_1(E_2472,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_48321])).

tff(c_48449,plain,(
    ! [E_2472] : ~ m1_subset_1(E_2472,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_48448])).

tff(c_48457,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48449,c_82])).

tff(c_48458,plain,(
    ! [D_2468] : ~ m1_subset_1(D_2468,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_48448])).

tff(c_48465,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48458,c_82])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:18:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.69/12.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.75/12.19  
% 22.75/12.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.75/12.19  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_enumset1 > k3_enumset1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_11 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_2 > #skF_12 > #skF_4
% 22.75/12.19  
% 22.75/12.19  %Foreground sorts:
% 22.75/12.19  
% 22.75/12.19  
% 22.75/12.19  %Background operators:
% 22.75/12.19  
% 22.75/12.19  
% 22.75/12.19  %Foreground operators:
% 22.75/12.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.75/12.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 22.75/12.19  tff('#skF_11', type, '#skF_11': $i).
% 22.75/12.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 22.75/12.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 22.75/12.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 22.75/12.19  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 22.75/12.19  tff('#skF_7', type, '#skF_7': $i).
% 22.75/12.19  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 22.75/12.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 22.75/12.19  tff('#skF_10', type, '#skF_10': $i).
% 22.75/12.19  tff('#skF_6', type, '#skF_6': $i).
% 22.75/12.19  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 22.75/12.19  tff('#skF_9', type, '#skF_9': $i).
% 22.75/12.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 22.75/12.19  tff('#skF_8', type, '#skF_8': $i).
% 22.75/12.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.75/12.19  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i * $i) > $i).
% 22.75/12.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.75/12.19  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 22.75/12.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 22.75/12.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 22.75/12.19  tff('#skF_12', type, '#skF_12': $i).
% 22.75/12.19  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i) > $i).
% 22.75/12.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 22.75/12.19  
% 22.75/12.21  tff(f_138, negated_conjecture, ~(![A, B]: (m1_subset_1(B, A) => (![C]: (m1_subset_1(C, A) => (![D]: (m1_subset_1(D, A) => (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, A) => (~(A = k1_xboole_0) => m1_subset_1(k4_enumset1(B, C, D, E, F, G), k1_zfmisc_1(A))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_subset_1)).
% 22.75/12.21  tff(f_115, axiom, (![A, B]: (m1_subset_1(B, A) => (![C]: (m1_subset_1(C, A) => (![D]: (m1_subset_1(D, A) => (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, A) => (~(A = k1_xboole_0) => m1_subset_1(k3_enumset1(B, C, D, E, F), k1_zfmisc_1(A))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_subset_1)).
% 22.75/12.21  tff(f_89, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 22.75/12.21  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 22.75/12.21  tff(f_48, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 22.75/12.21  tff(f_52, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 22.75/12.21  tff(f_39, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 22.75/12.21  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 22.75/12.21  tff(f_86, axiom, (![A, B, C, D, E, F]: ((F = k3_enumset1(A, B, C, D, E)) <=> (![G]: (r2_hidden(G, F) <=> ~((((~(G = A) & ~(G = B)) & ~(G = C)) & ~(G = D)) & ~(G = E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_enumset1)).
% 22.75/12.21  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 22.75/12.21  tff(f_96, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 22.75/12.21  tff(c_80, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_138])).
% 22.75/12.21  tff(c_90, plain, (m1_subset_1('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_138])).
% 22.75/12.21  tff(c_88, plain, (m1_subset_1('#skF_9', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_138])).
% 22.75/12.21  tff(c_86, plain, (m1_subset_1('#skF_10', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_138])).
% 22.75/12.21  tff(c_84, plain, (m1_subset_1('#skF_11', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_138])).
% 22.75/12.21  tff(c_82, plain, (m1_subset_1('#skF_12', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_138])).
% 22.75/12.21  tff(c_1702, plain, (![C_482, E_479, B_481, D_478, F_477, A_480]: (m1_subset_1(k3_enumset1(B_481, C_482, D_478, E_479, F_477), k1_zfmisc_1(A_480)) | k1_xboole_0=A_480 | ~m1_subset_1(F_477, A_480) | ~m1_subset_1(E_479, A_480) | ~m1_subset_1(D_478, A_480) | ~m1_subset_1(C_482, A_480) | ~m1_subset_1(B_481, A_480))), inference(cnfTransformation, [status(thm)], [f_115])).
% 22.75/12.21  tff(c_72, plain, (![A_38]: (~v1_xboole_0(k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 22.75/12.21  tff(c_181, plain, (![B_174, A_175]: (r2_hidden(B_174, A_175) | ~m1_subset_1(B_174, A_175) | v1_xboole_0(A_175))), inference(cnfTransformation, [status(thm)], [f_65])).
% 22.75/12.21  tff(c_12, plain, (![C_24, A_20]: (r1_tarski(C_24, A_20) | ~r2_hidden(C_24, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 22.75/12.21  tff(c_185, plain, (![B_174, A_20]: (r1_tarski(B_174, A_20) | ~m1_subset_1(B_174, k1_zfmisc_1(A_20)) | v1_xboole_0(k1_zfmisc_1(A_20)))), inference(resolution, [status(thm)], [c_181, c_12])).
% 22.75/12.21  tff(c_191, plain, (![B_174, A_20]: (r1_tarski(B_174, A_20) | ~m1_subset_1(B_174, k1_zfmisc_1(A_20)))), inference(negUnitSimplification, [status(thm)], [c_72, c_185])).
% 22.75/12.21  tff(c_26803, plain, (![A_1422, C_1420, D_1421, B_1419, F_1418, E_1417]: (r1_tarski(k3_enumset1(B_1419, C_1420, D_1421, E_1417, F_1418), A_1422) | k1_xboole_0=A_1422 | ~m1_subset_1(F_1418, A_1422) | ~m1_subset_1(E_1417, A_1422) | ~m1_subset_1(D_1421, A_1422) | ~m1_subset_1(C_1420, A_1422) | ~m1_subset_1(B_1419, A_1422))), inference(resolution, [status(thm)], [c_1702, c_191])).
% 22.75/12.21  tff(c_129, plain, (![B_147, A_148]: (v1_xboole_0(B_147) | ~m1_subset_1(B_147, A_148) | ~v1_xboole_0(A_148))), inference(cnfTransformation, [status(thm)], [f_65])).
% 22.75/12.21  tff(c_152, plain, (v1_xboole_0('#skF_12') | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_82, c_129])).
% 22.75/12.21  tff(c_158, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_152])).
% 22.75/12.21  tff(c_92, plain, (m1_subset_1('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_138])).
% 22.75/12.21  tff(c_30, plain, (![B_28, A_27]: (r2_hidden(B_28, A_27) | ~m1_subset_1(B_28, A_27) | v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_65])).
% 22.75/12.21  tff(c_26, plain, (![A_25, B_26]: (r1_tarski(k1_tarski(A_25), B_26) | ~r2_hidden(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_52])).
% 22.75/12.21  tff(c_578, plain, (![B_278, D_280, A_276, C_279, E_277, F_275]: (k2_xboole_0(k1_tarski(A_276), k3_enumset1(B_278, C_279, D_280, E_277, F_275))=k4_enumset1(A_276, B_278, C_279, D_280, E_277, F_275))), inference(cnfTransformation, [status(thm)], [f_39])).
% 22.75/12.21  tff(c_6, plain, (![A_5, C_7, B_6]: (r1_tarski(k2_xboole_0(A_5, C_7), B_6) | ~r1_tarski(C_7, B_6) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 22.75/12.21  tff(c_5779, plain, (![F_785, A_789, B_788, E_786, D_787, B_790, C_791]: (r1_tarski(k4_enumset1(A_789, B_790, C_791, D_787, E_786, F_785), B_788) | ~r1_tarski(k3_enumset1(B_790, C_791, D_787, E_786, F_785), B_788) | ~r1_tarski(k1_tarski(A_789), B_788))), inference(superposition, [status(thm), theory('equality')], [c_578, c_6])).
% 22.75/12.21  tff(c_14, plain, (![C_24, A_20]: (r2_hidden(C_24, k1_zfmisc_1(A_20)) | ~r1_tarski(C_24, A_20))), inference(cnfTransformation, [status(thm)], [f_48])).
% 22.75/12.21  tff(c_199, plain, (![B_178, A_179]: (m1_subset_1(B_178, A_179) | ~r2_hidden(B_178, A_179) | v1_xboole_0(A_179))), inference(cnfTransformation, [status(thm)], [f_65])).
% 22.75/12.21  tff(c_217, plain, (![C_24, A_20]: (m1_subset_1(C_24, k1_zfmisc_1(A_20)) | v1_xboole_0(k1_zfmisc_1(A_20)) | ~r1_tarski(C_24, A_20))), inference(resolution, [status(thm)], [c_14, c_199])).
% 22.75/12.21  tff(c_261, plain, (![C_186, A_187]: (m1_subset_1(C_186, k1_zfmisc_1(A_187)) | ~r1_tarski(C_186, A_187))), inference(negUnitSimplification, [status(thm)], [c_72, c_217])).
% 22.75/12.21  tff(c_78, plain, (~m1_subset_1(k4_enumset1('#skF_7', '#skF_8', '#skF_9', '#skF_10', '#skF_11', '#skF_12'), k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 22.75/12.21  tff(c_273, plain, (~r1_tarski(k4_enumset1('#skF_7', '#skF_8', '#skF_9', '#skF_10', '#skF_11', '#skF_12'), '#skF_6')), inference(resolution, [status(thm)], [c_261, c_78])).
% 22.75/12.21  tff(c_5845, plain, (~r1_tarski(k3_enumset1('#skF_8', '#skF_9', '#skF_10', '#skF_11', '#skF_12'), '#skF_6') | ~r1_tarski(k1_tarski('#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_5779, c_273])).
% 22.75/12.21  tff(c_5846, plain, (~r1_tarski(k1_tarski('#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_5845])).
% 22.75/12.21  tff(c_5850, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_26, c_5846])).
% 22.75/12.21  tff(c_5856, plain, (~m1_subset_1('#skF_7', '#skF_6') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_30, c_5850])).
% 22.75/12.21  tff(c_5860, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_5856])).
% 22.75/12.21  tff(c_5862, plain, $false, inference(negUnitSimplification, [status(thm)], [c_158, c_5860])).
% 22.75/12.21  tff(c_5863, plain, (~r1_tarski(k3_enumset1('#skF_8', '#skF_9', '#skF_10', '#skF_11', '#skF_12'), '#skF_6')), inference(splitRight, [status(thm)], [c_5845])).
% 22.75/12.21  tff(c_26897, plain, (k1_xboole_0='#skF_6' | ~m1_subset_1('#skF_12', '#skF_6') | ~m1_subset_1('#skF_11', '#skF_6') | ~m1_subset_1('#skF_10', '#skF_6') | ~m1_subset_1('#skF_9', '#skF_6') | ~m1_subset_1('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_26803, c_5863])).
% 22.75/12.21  tff(c_27023, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_84, c_82, c_26897])).
% 22.75/12.21  tff(c_27025, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_27023])).
% 22.75/12.21  tff(c_27027, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_152])).
% 22.75/12.21  tff(c_27038, plain, (![G_1427, D_1423, B_1424, E_1426, A_1425]: (r2_hidden(G_1427, k3_enumset1(A_1425, B_1424, G_1427, D_1423, E_1426)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 22.75/12.21  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 22.75/12.21  tff(c_27042, plain, (![G_1427, D_1423, B_1424, E_1426, A_1425]: (~v1_xboole_0(k3_enumset1(A_1425, B_1424, G_1427, D_1423, E_1426)))), inference(resolution, [status(thm)], [c_27038, c_2])).
% 22.75/12.21  tff(c_28219, plain, (![C_1702, B_1701, E_1699, F_1697, D_1698, A_1700]: (m1_subset_1(k3_enumset1(B_1701, C_1702, D_1698, E_1699, F_1697), k1_zfmisc_1(A_1700)) | k1_xboole_0=A_1700 | ~m1_subset_1(F_1697, A_1700) | ~m1_subset_1(E_1699, A_1700) | ~m1_subset_1(D_1698, A_1700) | ~m1_subset_1(C_1702, A_1700) | ~m1_subset_1(B_1701, A_1700))), inference(cnfTransformation, [status(thm)], [f_115])).
% 22.75/12.21  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 22.75/12.21  tff(c_27152, plain, (![C_1462, A_1463, B_1464]: (r2_hidden(C_1462, A_1463) | ~r2_hidden(C_1462, B_1464) | ~m1_subset_1(B_1464, k1_zfmisc_1(A_1463)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 22.75/12.21  tff(c_27203, plain, (![A_1493, A_1494]: (r2_hidden('#skF_1'(A_1493), A_1494) | ~m1_subset_1(A_1493, k1_zfmisc_1(A_1494)) | v1_xboole_0(A_1493))), inference(resolution, [status(thm)], [c_4, c_27152])).
% 22.75/12.21  tff(c_27219, plain, (![A_1494, A_1493]: (~v1_xboole_0(A_1494) | ~m1_subset_1(A_1493, k1_zfmisc_1(A_1494)) | v1_xboole_0(A_1493))), inference(resolution, [status(thm)], [c_27203, c_2])).
% 22.75/12.21  tff(c_28253, plain, (![C_1702, B_1701, E_1699, F_1697, D_1698, A_1700]: (~v1_xboole_0(A_1700) | v1_xboole_0(k3_enumset1(B_1701, C_1702, D_1698, E_1699, F_1697)) | k1_xboole_0=A_1700 | ~m1_subset_1(F_1697, A_1700) | ~m1_subset_1(E_1699, A_1700) | ~m1_subset_1(D_1698, A_1700) | ~m1_subset_1(C_1702, A_1700) | ~m1_subset_1(B_1701, A_1700))), inference(resolution, [status(thm)], [c_28219, c_27219])).
% 22.75/12.21  tff(c_48187, plain, (![F_2471, E_2472, B_2467, D_2468, A_2469, C_2470]: (~v1_xboole_0(A_2469) | k1_xboole_0=A_2469 | ~m1_subset_1(F_2471, A_2469) | ~m1_subset_1(E_2472, A_2469) | ~m1_subset_1(D_2468, A_2469) | ~m1_subset_1(C_2470, A_2469) | ~m1_subset_1(B_2467, A_2469))), inference(negUnitSimplification, [status(thm)], [c_27042, c_28253])).
% 22.75/12.21  tff(c_48247, plain, (![E_2472, D_2468, C_2470, B_2467]: (~v1_xboole_0('#skF_6') | k1_xboole_0='#skF_6' | ~m1_subset_1(E_2472, '#skF_6') | ~m1_subset_1(D_2468, '#skF_6') | ~m1_subset_1(C_2470, '#skF_6') | ~m1_subset_1(B_2467, '#skF_6'))), inference(resolution, [status(thm)], [c_82, c_48187])).
% 22.75/12.21  tff(c_48291, plain, (![E_2472, D_2468, C_2470, B_2467]: (k1_xboole_0='#skF_6' | ~m1_subset_1(E_2472, '#skF_6') | ~m1_subset_1(D_2468, '#skF_6') | ~m1_subset_1(C_2470, '#skF_6') | ~m1_subset_1(B_2467, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_27027, c_48247])).
% 22.75/12.21  tff(c_48292, plain, (![E_2472, D_2468, C_2470, B_2467]: (~m1_subset_1(E_2472, '#skF_6') | ~m1_subset_1(D_2468, '#skF_6') | ~m1_subset_1(C_2470, '#skF_6') | ~m1_subset_1(B_2467, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_80, c_48291])).
% 22.75/12.21  tff(c_48313, plain, (![B_2467]: (~m1_subset_1(B_2467, '#skF_6'))), inference(splitLeft, [status(thm)], [c_48292])).
% 22.75/12.21  tff(c_48320, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48313, c_82])).
% 22.75/12.21  tff(c_48321, plain, (![D_2468, E_2472, C_2470]: (~m1_subset_1(D_2468, '#skF_6') | ~m1_subset_1(E_2472, '#skF_6') | ~m1_subset_1(C_2470, '#skF_6'))), inference(splitRight, [status(thm)], [c_48292])).
% 22.75/12.21  tff(c_48440, plain, (![C_2470]: (~m1_subset_1(C_2470, '#skF_6'))), inference(splitLeft, [status(thm)], [c_48321])).
% 22.75/12.21  tff(c_48447, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48440, c_82])).
% 22.75/12.21  tff(c_48448, plain, (![D_2468, E_2472]: (~m1_subset_1(D_2468, '#skF_6') | ~m1_subset_1(E_2472, '#skF_6'))), inference(splitRight, [status(thm)], [c_48321])).
% 22.75/12.21  tff(c_48449, plain, (![E_2472]: (~m1_subset_1(E_2472, '#skF_6'))), inference(splitLeft, [status(thm)], [c_48448])).
% 22.75/12.21  tff(c_48457, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48449, c_82])).
% 22.75/12.21  tff(c_48458, plain, (![D_2468]: (~m1_subset_1(D_2468, '#skF_6'))), inference(splitRight, [status(thm)], [c_48448])).
% 22.75/12.21  tff(c_48465, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48458, c_82])).
% 22.75/12.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.75/12.21  
% 22.75/12.21  Inference rules
% 22.75/12.21  ----------------------
% 22.75/12.21  #Ref     : 0
% 22.75/12.21  #Sup     : 10540
% 22.75/12.21  #Fact    : 100
% 22.75/12.21  #Define  : 0
% 22.75/12.21  #Split   : 33
% 22.75/12.21  #Chain   : 0
% 22.75/12.21  #Close   : 0
% 22.75/12.21  
% 22.75/12.21  Ordering : KBO
% 22.75/12.21  
% 22.75/12.21  Simplification rules
% 22.75/12.21  ----------------------
% 22.75/12.21  #Subsume      : 1391
% 22.75/12.21  #Demod        : 199
% 22.75/12.21  #Tautology    : 350
% 22.75/12.21  #SimpNegUnit  : 2896
% 22.75/12.21  #BackRed      : 63
% 22.75/12.21  
% 22.75/12.21  #Partial instantiations: 0
% 22.75/12.21  #Strategies tried      : 1
% 22.75/12.21  
% 22.75/12.21  Timing (in seconds)
% 22.75/12.21  ----------------------
% 22.75/12.21  Preprocessing        : 0.37
% 22.75/12.21  Parsing              : 0.18
% 22.75/12.21  CNF conversion       : 0.04
% 22.75/12.21  Main loop            : 11.08
% 22.75/12.21  Inferencing          : 1.99
% 22.75/12.21  Reduction            : 2.05
% 22.75/12.21  Demodulation         : 1.28
% 22.75/12.21  BG Simplification    : 0.28
% 22.75/12.21  Subsumption          : 6.10
% 22.75/12.21  Abstraction          : 0.56
% 22.75/12.21  MUC search           : 0.00
% 22.75/12.21  Cooper               : 0.00
% 22.75/12.21  Total                : 11.48
% 22.75/12.21  Index Insertion      : 0.00
% 22.75/12.21  Index Deletion       : 0.00
% 22.75/12.21  Index Matching       : 0.00
% 22.75/12.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
