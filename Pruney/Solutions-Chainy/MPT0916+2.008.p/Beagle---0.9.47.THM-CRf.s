%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:10 EST 2020

% Result     : Theorem 12.85s
% Output     : CNFRefutation 13.64s
% Verified   : 
% Statistics : Number of formulae       :  595 (5871 expanded)
%              Number of leaves         :   42 (1917 expanded)
%              Depth                    :   18
%              Number of atoms          :  934 (13034 expanded)
%              Number of equality atoms :  387 (3171 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_55,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_127,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(A))
       => ! [E] :
            ( m1_subset_1(E,k1_zfmisc_1(B))
           => ! [F] :
                ( m1_subset_1(F,k1_zfmisc_1(C))
               => ! [G] :
                    ( m1_subset_1(G,k3_zfmisc_1(A,B,C))
                   => ( r2_hidden(G,k3_zfmisc_1(D,E,F))
                     => ( r2_hidden(k5_mcart_1(A,B,C,G),D)
                        & r2_hidden(k6_mcart_1(A,B,C,G),E)
                        & r2_hidden(k7_mcart_1(A,B,C,G),F) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_mcart_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_71,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_81,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(c_16,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_60,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_52550,plain,(
    ! [A_2599,B_2600] :
      ( r1_tarski(A_2599,B_2600)
      | ~ m1_subset_1(A_2599,k1_zfmisc_1(B_2600)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_52561,plain,(
    r1_tarski('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_52550])).

tff(c_54,plain,(
    m1_subset_1('#skF_9',k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_28,plain,(
    ! [A_21] : r1_tarski(k1_xboole_0,A_21) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_52974,plain,(
    ! [A_2630,C_2631,B_2632] :
      ( r1_xboole_0(A_2630,C_2631)
      | ~ r1_tarski(A_2630,k4_xboole_0(B_2632,C_2631)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_53018,plain,(
    ! [C_2633] : r1_xboole_0(k1_xboole_0,C_2633) ),
    inference(resolution,[status(thm)],[c_28,c_52974])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_53031,plain,(
    ! [C_2634] : r1_xboole_0(C_2634,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_53018,c_6])).

tff(c_30,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,B_23) = A_22
      | ~ r1_xboole_0(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_53041,plain,(
    ! [C_2634] : k4_xboole_0(C_2634,k1_xboole_0) = C_2634 ),
    inference(resolution,[status(thm)],[c_53031,c_30])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | k4_xboole_0(A_14,B_15) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_124,plain,(
    ! [A_65,B_66] :
      ( k4_xboole_0(A_65,B_66) = k1_xboole_0
      | ~ r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_136,plain,(
    ! [A_21] : k4_xboole_0(k1_xboole_0,A_21) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_124])).

tff(c_53190,plain,(
    ! [A_2643,A_2644] :
      ( r1_xboole_0(A_2643,A_2644)
      | ~ r1_tarski(A_2643,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_52974])).

tff(c_53323,plain,(
    ! [A_2654,A_2655] :
      ( r1_xboole_0(A_2654,A_2655)
      | ~ r1_tarski(A_2655,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_53190,c_6])).

tff(c_26,plain,(
    ! [A_19,B_20] :
      ( k3_xboole_0(A_19,B_20) = A_19
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_52578,plain,(
    k3_xboole_0('#skF_6','#skF_3') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_52561,c_26])).

tff(c_52832,plain,(
    ! [A_2618,B_2619,C_2620] :
      ( ~ r1_xboole_0(A_2618,B_2619)
      | ~ r2_hidden(C_2620,k3_xboole_0(A_2618,B_2619)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_52841,plain,(
    ! [C_2620] :
      ( ~ r1_xboole_0('#skF_6','#skF_3')
      | ~ r2_hidden(C_2620,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52578,c_52832])).

tff(c_53206,plain,(
    ~ r1_xboole_0('#skF_6','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_52841])).

tff(c_53342,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_53323,c_53206])).

tff(c_53354,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_53342])).

tff(c_53356,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53041,c_53354])).

tff(c_58,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_52562,plain,(
    r1_tarski('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_52550])).

tff(c_52586,plain,(
    k3_xboole_0('#skF_7','#skF_4') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_52562,c_26])).

tff(c_52835,plain,(
    ! [C_2620] :
      ( ~ r1_xboole_0('#skF_7','#skF_4')
      | ~ r2_hidden(C_2620,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52586,c_52832])).

tff(c_52860,plain,(
    ~ r1_xboole_0('#skF_7','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_52835])).

tff(c_53344,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_53323,c_52860])).

tff(c_53359,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_53344])).

tff(c_53361,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53041,c_53359])).

tff(c_56,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_52560,plain,(
    r1_tarski('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_52550])).

tff(c_52570,plain,(
    k3_xboole_0('#skF_8','#skF_5') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_52560,c_26])).

tff(c_52838,plain,(
    ! [C_2620] :
      ( ~ r1_xboole_0('#skF_8','#skF_5')
      | ~ r2_hidden(C_2620,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52570,c_52832])).

tff(c_53297,plain,(
    ~ r1_xboole_0('#skF_8','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_52838])).

tff(c_53341,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_53323,c_53297])).

tff(c_53349,plain,(
    k4_xboole_0('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_53341])).

tff(c_53351,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53041,c_53349])).

tff(c_53548,plain,(
    ! [A_2662,B_2663,C_2664,D_2665] :
      ( k7_mcart_1(A_2662,B_2663,C_2664,D_2665) = k2_mcart_1(D_2665)
      | ~ m1_subset_1(D_2665,k3_zfmisc_1(A_2662,B_2663,C_2664))
      | k1_xboole_0 = C_2664
      | k1_xboole_0 = B_2663
      | k1_xboole_0 = A_2662 ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_53551,plain,
    ( k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_54,c_53548])).

tff(c_53554,plain,(
    k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') = k2_mcart_1('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_53356,c_53361,c_53351,c_53551])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_49207,plain,(
    ! [A_2452,B_2453,C_2454] :
      ( r2_hidden(k1_mcart_1(A_2452),B_2453)
      | ~ r2_hidden(A_2452,k2_zfmisc_1(B_2453,C_2454)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_52434,plain,(
    ! [B_2594,C_2595] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_2594,C_2595))),B_2594)
      | v1_xboole_0(k2_zfmisc_1(B_2594,C_2595)) ) ),
    inference(resolution,[status(thm)],[c_4,c_49207])).

tff(c_50,plain,
    ( ~ r2_hidden(k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_8')
    | ~ r2_hidden(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_7')
    | ~ r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_144,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_255,plain,(
    ! [A_78,C_79,B_80] :
      ( r1_xboole_0(A_78,C_79)
      | ~ r1_tarski(A_78,k4_xboole_0(B_80,C_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_286,plain,(
    ! [C_81] : r1_xboole_0(k1_xboole_0,C_81) ),
    inference(resolution,[status(thm)],[c_28,c_255])).

tff(c_295,plain,(
    ! [C_82] : r1_xboole_0(C_82,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_286,c_6])).

tff(c_301,plain,(
    ! [C_82] : k4_xboole_0(C_82,k1_xboole_0) = C_82 ),
    inference(resolution,[status(thm)],[c_295,c_30])).

tff(c_135,plain,(
    ! [B_13] : k4_xboole_0(B_13,B_13) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_124])).

tff(c_412,plain,(
    ! [A_88,B_89,C_90] :
      ( r1_tarski(A_88,B_89)
      | ~ r1_tarski(A_88,k4_xboole_0(B_89,C_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_24930,plain,(
    ! [A_1227,B_1228] :
      ( r1_tarski(A_1227,B_1228)
      | ~ r1_tarski(A_1227,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_412])).

tff(c_24936,plain,(
    ! [A_14,B_1228] :
      ( r1_tarski(A_14,B_1228)
      | k4_xboole_0(A_14,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_24930])).

tff(c_24953,plain,(
    ! [A_1229,B_1230] :
      ( r1_tarski(A_1229,B_1230)
      | k1_xboole_0 != A_1229 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_24936])).

tff(c_160,plain,(
    ! [A_69,B_70] :
      ( r1_tarski(A_69,B_70)
      | ~ m1_subset_1(A_69,k1_zfmisc_1(B_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_171,plain,(
    r1_tarski('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_160])).

tff(c_557,plain,(
    ! [B_100,A_101] :
      ( B_100 = A_101
      | ~ r1_tarski(B_100,A_101)
      | ~ r1_tarski(A_101,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_574,plain,
    ( '#skF_6' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_6') ),
    inference(resolution,[status(thm)],[c_171,c_557])).

tff(c_24782,plain,(
    ~ r1_tarski('#skF_3','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_574])).

tff(c_24989,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(resolution,[status(thm)],[c_24953,c_24782])).

tff(c_749,plain,(
    ! [A_114,B_115] :
      ( r1_tarski(A_114,B_115)
      | ~ r1_tarski(A_114,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_412])).

tff(c_755,plain,(
    ! [A_14,B_115] :
      ( r1_tarski(A_14,B_115)
      | k4_xboole_0(A_14,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_749])).

tff(c_772,plain,(
    ! [A_116,B_117] :
      ( r1_tarski(A_116,B_117)
      | k1_xboole_0 != A_116 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_755])).

tff(c_612,plain,(
    ~ r1_tarski('#skF_3','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_574])).

tff(c_811,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(resolution,[status(thm)],[c_772,c_612])).

tff(c_172,plain,(
    r1_tarski('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_160])).

tff(c_573,plain,
    ( '#skF_7' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_7') ),
    inference(resolution,[status(thm)],[c_172,c_557])).

tff(c_607,plain,(
    ~ r1_tarski('#skF_4','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_573])).

tff(c_812,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_772,c_607])).

tff(c_170,plain,(
    r1_tarski('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_160])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = k1_xboole_0
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_179,plain,(
    k4_xboole_0('#skF_8','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_170,c_20])).

tff(c_515,plain,(
    ! [A_96] :
      ( r1_tarski(A_96,'#skF_8')
      | ~ r1_tarski(A_96,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_412])).

tff(c_523,plain,(
    ! [A_14] :
      ( r1_tarski(A_14,'#skF_8')
      | k4_xboole_0(A_14,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_515])).

tff(c_628,plain,(
    ! [A_106] :
      ( r1_tarski(A_106,'#skF_8')
      | k1_xboole_0 != A_106 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_523])).

tff(c_575,plain,
    ( '#skF_5' = '#skF_8'
    | ~ r1_tarski('#skF_5','#skF_8') ),
    inference(resolution,[status(thm)],[c_170,c_557])).

tff(c_617,plain,(
    ~ r1_tarski('#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_575])).

tff(c_640,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(resolution,[status(thm)],[c_628,c_617])).

tff(c_1277,plain,(
    ! [A_140,B_141,C_142,D_143] :
      ( k5_mcart_1(A_140,B_141,C_142,D_143) = k1_mcart_1(k1_mcart_1(D_143))
      | ~ m1_subset_1(D_143,k3_zfmisc_1(A_140,B_141,C_142))
      | k1_xboole_0 = C_142
      | k1_xboole_0 = B_141
      | k1_xboole_0 = A_140 ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1280,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_54,c_1277])).

tff(c_1283,plain,(
    k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_811,c_812,c_640,c_1280])).

tff(c_52,plain,(
    r2_hidden('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_38,plain,(
    ! [A_26,B_27,C_28] : k2_zfmisc_1(k2_zfmisc_1(A_26,B_27),C_28) = k3_zfmisc_1(A_26,B_27,C_28) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_842,plain,(
    ! [A_118,B_119,C_120] :
      ( r2_hidden(k1_mcart_1(A_118),B_119)
      | ~ r2_hidden(A_118,k2_zfmisc_1(B_119,C_120)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_4017,plain,(
    ! [A_265,A_266,B_267,C_268] :
      ( r2_hidden(k1_mcart_1(A_265),k2_zfmisc_1(A_266,B_267))
      | ~ r2_hidden(A_265,k3_zfmisc_1(A_266,B_267,C_268)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_842])).

tff(c_4045,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_52,c_4017])).

tff(c_42,plain,(
    ! [A_29,B_30,C_31] :
      ( r2_hidden(k1_mcart_1(A_29),B_30)
      | ~ r2_hidden(A_29,k2_zfmisc_1(B_30,C_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_4051,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_4045,c_42])).

tff(c_4065,plain,(
    r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1283,c_4051])).

tff(c_4067,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_4065])).

tff(c_4068,plain,(
    '#skF_5' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_575])).

tff(c_4071,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_8','#skF_9'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4068,c_144])).

tff(c_4192,plain,(
    ! [A_277,B_278] :
      ( r1_tarski(A_277,B_278)
      | ~ r1_tarski(A_277,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_412])).

tff(c_4198,plain,(
    ! [A_14,B_278] :
      ( r1_tarski(A_14,B_278)
      | k4_xboole_0(A_14,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_4192])).

tff(c_4215,plain,(
    ! [A_279,B_280] :
      ( r1_tarski(A_279,B_280)
      | k1_xboole_0 != A_279 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_4198])).

tff(c_4250,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(resolution,[status(thm)],[c_4215,c_612])).

tff(c_4251,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_4215,c_607])).

tff(c_4074,plain,(
    m1_subset_1('#skF_9',k3_zfmisc_1('#skF_3','#skF_4','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4068,c_54])).

tff(c_4700,plain,(
    ! [A_304,B_305,C_306,D_307] :
      ( k7_mcart_1(A_304,B_305,C_306,D_307) = k2_mcart_1(D_307)
      | ~ m1_subset_1(D_307,k3_zfmisc_1(A_304,B_305,C_306))
      | k1_xboole_0 = C_306
      | k1_xboole_0 = B_305
      | k1_xboole_0 = A_304 ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_4703,plain,
    ( k7_mcart_1('#skF_3','#skF_4','#skF_8','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4074,c_4700])).

tff(c_4706,plain,
    ( k7_mcart_1('#skF_3','#skF_4','#skF_8','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_4250,c_4251,c_4703])).

tff(c_4707,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_4706])).

tff(c_294,plain,(
    ! [C_81] : r1_xboole_0(C_81,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_286,c_6])).

tff(c_76,plain,(
    ! [A_57,B_58] :
      ( k3_xboole_0(A_57,B_58) = A_57
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_87,plain,(
    ! [B_13] : k3_xboole_0(B_13,B_13) = B_13 ),
    inference(resolution,[status(thm)],[c_16,c_76])).

tff(c_234,plain,(
    ! [A_75,B_76,C_77] :
      ( ~ r1_xboole_0(A_75,B_76)
      | ~ r2_hidden(C_77,k3_xboole_0(A_75,B_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_490,plain,(
    ! [B_93,C_94] :
      ( ~ r1_xboole_0(B_93,B_93)
      | ~ r2_hidden(C_94,B_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_234])).

tff(c_503,plain,(
    ! [C_94] : ~ r2_hidden(C_94,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_294,c_490])).

tff(c_4734,plain,(
    ! [C_94] : ~ r2_hidden(C_94,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4707,c_503])).

tff(c_4334,plain,(
    ! [A_292,B_293,C_294] : k2_zfmisc_1(k2_zfmisc_1(A_292,B_293),C_294) = k3_zfmisc_1(A_292,B_293,C_294) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_40,plain,(
    ! [A_29,C_31,B_30] :
      ( r2_hidden(k2_mcart_1(A_29),C_31)
      | ~ r2_hidden(A_29,k2_zfmisc_1(B_30,C_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_6032,plain,(
    ! [A_375,C_376,A_377,B_378] :
      ( r2_hidden(k2_mcart_1(A_375),C_376)
      | ~ r2_hidden(A_375,k3_zfmisc_1(A_377,B_378,C_376)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4334,c_40])).

tff(c_6034,plain,(
    r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_52,c_6032])).

tff(c_6041,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4734,c_6034])).

tff(c_6043,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_4706])).

tff(c_6337,plain,(
    ! [A_389,B_390,C_391,D_392] :
      ( k5_mcart_1(A_389,B_390,C_391,D_392) = k1_mcart_1(k1_mcart_1(D_392))
      | ~ m1_subset_1(D_392,k3_zfmisc_1(A_389,B_390,C_391))
      | k1_xboole_0 = C_391
      | k1_xboole_0 = B_390
      | k1_xboole_0 = A_389 ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_6340,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_8','#skF_9')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4074,c_6337])).

tff(c_6343,plain,(
    k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_4250,c_4251,c_6043,c_6340])).

tff(c_9943,plain,(
    ! [A_525,A_526,B_527,C_528] :
      ( r2_hidden(k1_mcart_1(A_525),k2_zfmisc_1(A_526,B_527))
      | ~ r2_hidden(A_525,k3_zfmisc_1(A_526,B_527,C_528)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4334,c_42])).

tff(c_9967,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_52,c_9943])).

tff(c_9975,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_9967,c_42])).

tff(c_9992,plain,(
    r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_8','#skF_9'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6343,c_9975])).

tff(c_9994,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4071,c_9992])).

tff(c_9995,plain,(
    '#skF_6' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_574])).

tff(c_9999,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9995,c_144])).

tff(c_10043,plain,(
    ! [A_530,B_531,C_532] :
      ( r2_hidden(k1_mcart_1(A_530),B_531)
      | ~ r2_hidden(A_530,k2_zfmisc_1(B_531,C_532)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_13459,plain,(
    ! [B_696,C_697] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_696,C_697))),B_696)
      | v1_xboole_0(k2_zfmisc_1(B_696,C_697)) ) ),
    inference(resolution,[status(thm)],[c_4,c_10043])).

tff(c_10120,plain,(
    ! [A_535,B_536] :
      ( r1_tarski(A_535,B_536)
      | ~ r1_tarski(A_535,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_412])).

tff(c_10126,plain,(
    ! [A_14,B_536] :
      ( r1_tarski(A_14,B_536)
      | k4_xboole_0(A_14,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_10120])).

tff(c_10143,plain,(
    ! [A_537,B_538] :
      ( r1_tarski(A_537,B_538)
      | k1_xboole_0 != A_537 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_10126])).

tff(c_10175,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_10143,c_607])).

tff(c_10027,plain,(
    ! [A_529] :
      ( r1_tarski(A_529,'#skF_8')
      | k1_xboole_0 != A_529 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_523])).

tff(c_10018,plain,(
    ~ r1_tarski('#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_575])).

tff(c_10039,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(resolution,[status(thm)],[c_10027,c_10018])).

tff(c_10393,plain,(
    ! [A_555,B_556,C_557,D_558] :
      ( k7_mcart_1(A_555,B_556,C_557,D_558) = k2_mcart_1(D_558)
      | ~ m1_subset_1(D_558,k3_zfmisc_1(A_555,B_556,C_557))
      | k1_xboole_0 = C_557
      | k1_xboole_0 = B_556
      | k1_xboole_0 = A_555 ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_10396,plain,
    ( k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_54,c_10393])).

tff(c_10399,plain,
    ( k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_10175,c_10039,c_10396])).

tff(c_10867,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_10399])).

tff(c_10897,plain,(
    ! [C_94] : ~ r2_hidden(C_94,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10867,c_503])).

tff(c_13504,plain,(
    ! [C_698] : v1_xboole_0(k2_zfmisc_1('#skF_3',C_698)) ),
    inference(resolution,[status(thm)],[c_13459,c_10897])).

tff(c_10901,plain,(
    ! [B_13] : k4_xboole_0(B_13,B_13) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10867,c_135])).

tff(c_10302,plain,(
    ! [A_551,B_552] :
      ( r2_hidden('#skF_2'(A_551,B_552),k3_xboole_0(A_551,B_552))
      | r1_xboole_0(A_551,B_552) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_11279,plain,(
    ! [A_592,B_593] :
      ( ~ v1_xboole_0(k3_xboole_0(A_592,B_593))
      | r1_xboole_0(A_592,B_593) ) ),
    inference(resolution,[status(thm)],[c_10302,c_2])).

tff(c_11329,plain,(
    ! [B_595] :
      ( ~ v1_xboole_0(B_595)
      | r1_xboole_0(B_595,B_595) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_11279])).

tff(c_11337,plain,(
    ! [B_595] :
      ( k4_xboole_0(B_595,B_595) = B_595
      | ~ v1_xboole_0(B_595) ) ),
    inference(resolution,[status(thm)],[c_11329,c_30])).

tff(c_11343,plain,(
    ! [B_595] :
      ( B_595 = '#skF_3'
      | ~ v1_xboole_0(B_595) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10901,c_11337])).

tff(c_13514,plain,(
    ! [C_698] : k2_zfmisc_1('#skF_3',C_698) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_13504,c_11343])).

tff(c_13518,plain,(
    ! [C_699] : k2_zfmisc_1('#skF_3',C_699) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_13504,c_11343])).

tff(c_13540,plain,(
    ! [C_699,C_28] : k3_zfmisc_1('#skF_3',C_699,C_28) = k2_zfmisc_1('#skF_3',C_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_13518,c_38])).

tff(c_13555,plain,(
    ! [C_699,C_28] : k3_zfmisc_1('#skF_3',C_699,C_28) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13514,c_13540])).

tff(c_10003,plain,(
    r2_hidden('#skF_9',k3_zfmisc_1('#skF_3','#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9995,c_52])).

tff(c_10235,plain,(
    ! [A_546,B_547] :
      ( r1_xboole_0(A_546,B_547)
      | ~ r1_tarski(A_546,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_255])).

tff(c_249,plain,(
    ! [B_13,C_77] :
      ( ~ r1_xboole_0(B_13,B_13)
      | ~ r2_hidden(C_77,B_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_234])).

tff(c_10400,plain,(
    ! [C_559,B_560] :
      ( ~ r2_hidden(C_559,B_560)
      | ~ r1_tarski(B_560,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10235,c_249])).

tff(c_10419,plain,(
    ~ r1_tarski(k3_zfmisc_1('#skF_3','#skF_7','#skF_8'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10003,c_10400])).

tff(c_10873,plain,(
    ~ r1_tarski(k3_zfmisc_1('#skF_3','#skF_7','#skF_8'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10867,c_10419])).

tff(c_13559,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13555,c_10873])).

tff(c_13567,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_13559])).

tff(c_13569,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_10399])).

tff(c_13630,plain,(
    ! [A_702,B_703,C_704,D_705] :
      ( k5_mcart_1(A_702,B_703,C_704,D_705) = k1_mcart_1(k1_mcart_1(D_705))
      | ~ m1_subset_1(D_705,k3_zfmisc_1(A_702,B_703,C_704))
      | k1_xboole_0 = C_704
      | k1_xboole_0 = B_703
      | k1_xboole_0 = A_702 ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_13633,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_54,c_13630])).

tff(c_13636,plain,(
    k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_13569,c_10175,c_10039,c_13633])).

tff(c_10182,plain,(
    ! [A_539,B_540,C_541] : k2_zfmisc_1(k2_zfmisc_1(A_539,B_540),C_541) = k3_zfmisc_1(A_539,B_540,C_541) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_16727,plain,(
    ! [A_854,A_855,B_856,C_857] :
      ( r2_hidden(k1_mcart_1(A_854),k2_zfmisc_1(A_855,B_856))
      | ~ r2_hidden(A_854,k3_zfmisc_1(A_855,B_856,C_857)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10182,c_42])).

tff(c_16754,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k2_zfmisc_1('#skF_3','#skF_7')) ),
    inference(resolution,[status(thm)],[c_10003,c_16727])).

tff(c_16762,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_16754,c_42])).

tff(c_16779,plain,(
    r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13636,c_16762])).

tff(c_16781,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9999,c_16779])).

tff(c_16782,plain,(
    '#skF_5' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_575])).

tff(c_17017,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_8','#skF_9'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16782,c_9999])).

tff(c_17010,plain,(
    ! [A_874,B_875,C_876] :
      ( r2_hidden(k1_mcart_1(A_874),B_875)
      | ~ r2_hidden(A_874,k2_zfmisc_1(B_875,C_876)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_18847,plain,(
    ! [B_981,C_982] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_981,C_982))),B_981)
      | v1_xboole_0(k2_zfmisc_1(B_981,C_982)) ) ),
    inference(resolution,[status(thm)],[c_4,c_17010])).

tff(c_16845,plain,(
    ! [A_864,B_865] :
      ( r1_tarski(A_864,B_865)
      | ~ r1_tarski(A_864,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_412])).

tff(c_16851,plain,(
    ! [A_14,B_865] :
      ( r1_tarski(A_14,B_865)
      | k4_xboole_0(A_14,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_16845])).

tff(c_16876,plain,(
    ! [A_866,B_867] :
      ( r1_tarski(A_866,B_867)
      | k1_xboole_0 != A_866 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_16851])).

tff(c_16908,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_16876,c_607])).

tff(c_16787,plain,(
    m1_subset_1('#skF_9',k3_zfmisc_1('#skF_3','#skF_4','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16782,c_54])).

tff(c_17536,plain,(
    ! [A_898,B_899,C_900,D_901] :
      ( k7_mcart_1(A_898,B_899,C_900,D_901) = k2_mcart_1(D_901)
      | ~ m1_subset_1(D_901,k3_zfmisc_1(A_898,B_899,C_900))
      | k1_xboole_0 = C_900
      | k1_xboole_0 = B_899
      | k1_xboole_0 = A_898 ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_17539,plain,
    ( k7_mcart_1('#skF_3','#skF_4','#skF_8','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_16787,c_17536])).

tff(c_17542,plain,
    ( k7_mcart_1('#skF_3','#skF_4','#skF_8','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_16908,c_17539])).

tff(c_17606,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_17542])).

tff(c_17630,plain,(
    ! [C_94] : ~ r2_hidden(C_94,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17606,c_503])).

tff(c_18892,plain,(
    ! [C_983] : v1_xboole_0(k2_zfmisc_1('#skF_3',C_983)) ),
    inference(resolution,[status(thm)],[c_18847,c_17630])).

tff(c_17633,plain,(
    ! [B_13] : k4_xboole_0(B_13,B_13) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17606,c_135])).

tff(c_17230,plain,(
    ! [A_890,B_891] :
      ( r2_hidden('#skF_2'(A_890,B_891),k3_xboole_0(A_890,B_891))
      | r1_xboole_0(A_890,B_891) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_17587,plain,(
    ! [A_905,B_906] :
      ( ~ v1_xboole_0(k3_xboole_0(A_905,B_906))
      | r1_xboole_0(A_905,B_906) ) ),
    inference(resolution,[status(thm)],[c_17230,c_2])).

tff(c_17975,plain,(
    ! [B_926] :
      ( ~ v1_xboole_0(B_926)
      | r1_xboole_0(B_926,B_926) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_17587])).

tff(c_17983,plain,(
    ! [B_926] :
      ( k4_xboole_0(B_926,B_926) = B_926
      | ~ v1_xboole_0(B_926) ) ),
    inference(resolution,[status(thm)],[c_17975,c_30])).

tff(c_17989,plain,(
    ! [B_926] :
      ( B_926 = '#skF_3'
      | ~ v1_xboole_0(B_926) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17633,c_17983])).

tff(c_18899,plain,(
    ! [C_983] : k2_zfmisc_1('#skF_3',C_983) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_18892,c_17989])).

tff(c_18903,plain,(
    ! [C_984] : k2_zfmisc_1('#skF_3',C_984) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_18892,c_17989])).

tff(c_18923,plain,(
    ! [C_984,C_28] : k3_zfmisc_1('#skF_3',C_984,C_28) = k2_zfmisc_1('#skF_3',C_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_18903,c_38])).

tff(c_18940,plain,(
    ! [C_984,C_28] : k3_zfmisc_1('#skF_3',C_984,C_28) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18899,c_18923])).

tff(c_16824,plain,(
    ! [A_862,B_863] :
      ( r1_xboole_0(A_862,B_863)
      | ~ r1_tarski(A_862,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_255])).

tff(c_17168,plain,(
    ! [C_885,B_886] :
      ( ~ r2_hidden(C_885,B_886)
      | ~ r1_tarski(B_886,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16824,c_249])).

tff(c_17175,plain,(
    ~ r1_tarski(k3_zfmisc_1('#skF_3','#skF_7','#skF_8'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10003,c_17168])).

tff(c_17610,plain,(
    ~ r1_tarski(k3_zfmisc_1('#skF_3','#skF_7','#skF_8'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17606,c_17175])).

tff(c_18944,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18940,c_17610])).

tff(c_18952,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18944])).

tff(c_18954,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_17542])).

tff(c_19161,plain,(
    ! [A_995,B_996,C_997,D_998] :
      ( k5_mcart_1(A_995,B_996,C_997,D_998) = k1_mcart_1(k1_mcart_1(D_998))
      | ~ m1_subset_1(D_998,k3_zfmisc_1(A_995,B_996,C_997))
      | k1_xboole_0 = C_997
      | k1_xboole_0 = B_996
      | k1_xboole_0 = A_995 ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_19164,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_8','#skF_9')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_16787,c_19161])).

tff(c_19167,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_8','#skF_9')
    | k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_18954,c_16908,c_19164])).

tff(c_19262,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_19167])).

tff(c_19292,plain,(
    ! [C_94] : ~ r2_hidden(C_94,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19262,c_503])).

tff(c_17088,plain,(
    ! [A_879,B_880,C_881] : k2_zfmisc_1(k2_zfmisc_1(A_879,B_880),C_881) = k3_zfmisc_1(A_879,B_880,C_881) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_20021,plain,(
    ! [A_1037,C_1038,A_1039,B_1040] :
      ( r2_hidden(k2_mcart_1(A_1037),C_1038)
      | ~ r2_hidden(A_1037,k3_zfmisc_1(A_1039,B_1040,C_1038)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17088,c_40])).

tff(c_20023,plain,(
    r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_10003,c_20021])).

tff(c_20030,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19292,c_20023])).

tff(c_20031,plain,(
    k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_19167])).

tff(c_24694,plain,(
    ! [A_1212,A_1213,B_1214,C_1215] :
      ( r2_hidden(k1_mcart_1(A_1212),k2_zfmisc_1(A_1213,B_1214))
      | ~ r2_hidden(A_1212,k3_zfmisc_1(A_1213,B_1214,C_1215)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17088,c_42])).

tff(c_24721,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k2_zfmisc_1('#skF_3','#skF_7')) ),
    inference(resolution,[status(thm)],[c_10003,c_24694])).

tff(c_24727,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_24721,c_42])).

tff(c_24744,plain,(
    r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_8','#skF_9'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20031,c_24727])).

tff(c_24746,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17017,c_24744])).

tff(c_24747,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_573])).

tff(c_116,plain,(
    ! [A_63,B_64] :
      ( r1_xboole_0(A_63,B_64)
      | k4_xboole_0(A_63,B_64) != A_63 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_123,plain,(
    ! [B_64,A_63] :
      ( r1_xboole_0(B_64,A_63)
      | k4_xboole_0(A_63,B_64) != A_63 ) ),
    inference(resolution,[status(thm)],[c_116,c_6])).

tff(c_196,plain,(
    k3_xboole_0('#skF_7','#skF_4') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_172,c_26])).

tff(c_237,plain,(
    ! [C_77] :
      ( ~ r1_xboole_0('#skF_7','#skF_4')
      | ~ r2_hidden(C_77,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_234])).

tff(c_337,plain,(
    ~ r1_xboole_0('#skF_7','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_237])).

tff(c_344,plain,(
    k4_xboole_0('#skF_4','#skF_7') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_123,c_337])).

tff(c_24749,plain,(
    k4_xboole_0('#skF_4','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24747,c_344])).

tff(c_24758,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_24749])).

tff(c_24802,plain,(
    ! [A_1219] :
      ( r1_tarski(A_1219,'#skF_8')
      | k1_xboole_0 != A_1219 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_523])).

tff(c_24792,plain,(
    ~ r1_tarski('#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_575])).

tff(c_24814,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(resolution,[status(thm)],[c_24802,c_24792])).

tff(c_25274,plain,(
    ! [A_1249,B_1250,C_1251,D_1252] :
      ( k5_mcart_1(A_1249,B_1250,C_1251,D_1252) = k1_mcart_1(k1_mcart_1(D_1252))
      | ~ m1_subset_1(D_1252,k3_zfmisc_1(A_1249,B_1250,C_1251))
      | k1_xboole_0 = C_1251
      | k1_xboole_0 = B_1250
      | k1_xboole_0 = A_1249 ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_25277,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_54,c_25274])).

tff(c_25280,plain,(
    k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_24989,c_24758,c_24814,c_25277])).

tff(c_24756,plain,(
    r2_hidden('#skF_9',k3_zfmisc_1('#skF_6','#skF_4','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24747,c_52])).

tff(c_24996,plain,(
    ! [A_1231,B_1232,C_1233] :
      ( r2_hidden(k1_mcart_1(A_1231),B_1232)
      | ~ r2_hidden(A_1231,k2_zfmisc_1(B_1232,C_1233)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_28147,plain,(
    ! [A_1399,A_1400,B_1401,C_1402] :
      ( r2_hidden(k1_mcart_1(A_1399),k2_zfmisc_1(A_1400,B_1401))
      | ~ r2_hidden(A_1399,k3_zfmisc_1(A_1400,B_1401,C_1402)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_24996])).

tff(c_28174,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k2_zfmisc_1('#skF_6','#skF_4')) ),
    inference(resolution,[status(thm)],[c_24756,c_28147])).

tff(c_28180,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_28174,c_42])).

tff(c_28197,plain,(
    r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25280,c_28180])).

tff(c_28199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_28197])).

tff(c_28200,plain,(
    '#skF_5' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_575])).

tff(c_28203,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_8','#skF_9'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28200,c_144])).

tff(c_28344,plain,(
    ! [A_1411,B_1412] :
      ( r1_tarski(A_1411,B_1412)
      | ~ r1_tarski(A_1411,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_412])).

tff(c_28350,plain,(
    ! [A_14,B_1412] :
      ( r1_tarski(A_14,B_1412)
      | k4_xboole_0(A_14,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_28344])).

tff(c_28367,plain,(
    ! [A_1413,B_1414] :
      ( r1_tarski(A_1413,B_1414)
      | k1_xboole_0 != A_1413 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_28350])).

tff(c_28399,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(resolution,[status(thm)],[c_28367,c_24782])).

tff(c_28206,plain,(
    m1_subset_1('#skF_9',k3_zfmisc_1('#skF_3','#skF_4','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28200,c_54])).

tff(c_28604,plain,(
    ! [A_1428,B_1429,C_1430,D_1431] :
      ( k7_mcart_1(A_1428,B_1429,C_1430,D_1431) = k2_mcart_1(D_1431)
      | ~ m1_subset_1(D_1431,k3_zfmisc_1(A_1428,B_1429,C_1430))
      | k1_xboole_0 = C_1430
      | k1_xboole_0 = B_1429
      | k1_xboole_0 = A_1428 ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_28607,plain,
    ( k7_mcart_1('#skF_3','#skF_4','#skF_8','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_28206,c_28604])).

tff(c_28610,plain,
    ( k7_mcart_1('#skF_3','#skF_4','#skF_8','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_28399,c_24758,c_28607])).

tff(c_29166,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_28610])).

tff(c_29196,plain,(
    ! [C_94] : ~ r2_hidden(C_94,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29166,c_503])).

tff(c_28239,plain,(
    ! [A_1404,B_1405,C_1406] : k2_zfmisc_1(k2_zfmisc_1(A_1404,B_1405),C_1406) = k3_zfmisc_1(A_1404,B_1405,C_1406) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_29804,plain,(
    ! [A_1486,C_1487,A_1488,B_1489] :
      ( r2_hidden(k2_mcart_1(A_1486),C_1487)
      | ~ r2_hidden(A_1486,k3_zfmisc_1(A_1488,B_1489,C_1487)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28239,c_40])).

tff(c_29806,plain,(
    r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_24756,c_29804])).

tff(c_29813,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_29196,c_29806])).

tff(c_29815,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_28610])).

tff(c_28858,plain,(
    ! [A_1441,B_1442,C_1443,D_1444] :
      ( k5_mcart_1(A_1441,B_1442,C_1443,D_1444) = k1_mcart_1(k1_mcart_1(D_1444))
      | ~ m1_subset_1(D_1444,k3_zfmisc_1(A_1441,B_1442,C_1443))
      | k1_xboole_0 = C_1443
      | k1_xboole_0 = B_1442
      | k1_xboole_0 = A_1441 ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_28861,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_8','#skF_9')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_28206,c_28858])).

tff(c_28864,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_8','#skF_9')
    | k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_28399,c_24758,c_28861])).

tff(c_29902,plain,(
    k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_29815,c_28864])).

tff(c_28424,plain,(
    ! [A_1417,B_1418,C_1419] :
      ( r2_hidden(k1_mcart_1(A_1417),B_1418)
      | ~ r2_hidden(A_1417,k2_zfmisc_1(B_1418,C_1419)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_32970,plain,(
    ! [A_1640,A_1641,B_1642,C_1643] :
      ( r2_hidden(k1_mcart_1(A_1640),k2_zfmisc_1(A_1641,B_1642))
      | ~ r2_hidden(A_1640,k3_zfmisc_1(A_1641,B_1642,C_1643)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_28424])).

tff(c_32997,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k2_zfmisc_1('#skF_6','#skF_4')) ),
    inference(resolution,[status(thm)],[c_24756,c_32970])).

tff(c_33003,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_32997,c_42])).

tff(c_33020,plain,(
    r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_8','#skF_9'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29902,c_33003])).

tff(c_33022,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28203,c_33020])).

tff(c_33023,plain,(
    '#skF_6' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_574])).

tff(c_33026,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33023,c_144])).

tff(c_33069,plain,(
    ! [A_1645,B_1646,C_1647] :
      ( r2_hidden(k1_mcart_1(A_1645),B_1646)
      | ~ r2_hidden(A_1645,k2_zfmisc_1(B_1646,C_1647)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_36287,plain,(
    ! [B_1825,C_1826] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_1825,C_1826))),B_1825)
      | v1_xboole_0(k2_zfmisc_1(B_1825,C_1826)) ) ),
    inference(resolution,[status(thm)],[c_4,c_33069])).

tff(c_33053,plain,(
    ! [A_1644] :
      ( r1_tarski(A_1644,'#skF_8')
      | k1_xboole_0 != A_1644 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_523])).

tff(c_33043,plain,(
    ~ r1_tarski('#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_575])).

tff(c_33065,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(resolution,[status(thm)],[c_33053,c_33043])).

tff(c_33529,plain,(
    ! [A_1677,B_1678,C_1679,D_1680] :
      ( k7_mcart_1(A_1677,B_1678,C_1679,D_1680) = k2_mcart_1(D_1680)
      | ~ m1_subset_1(D_1680,k3_zfmisc_1(A_1677,B_1678,C_1679))
      | k1_xboole_0 = C_1679
      | k1_xboole_0 = B_1678
      | k1_xboole_0 = A_1677 ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_33532,plain,
    ( k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_54,c_33529])).

tff(c_33535,plain,
    ( k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_24758,c_33065,c_33532])).

tff(c_33627,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_33535])).

tff(c_33652,plain,(
    ! [C_94] : ~ r2_hidden(C_94,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33627,c_503])).

tff(c_36337,plain,(
    ! [C_1827] : v1_xboole_0(k2_zfmisc_1('#skF_3',C_1827)) ),
    inference(resolution,[status(thm)],[c_36287,c_33652])).

tff(c_33655,plain,(
    ! [B_13] : k4_xboole_0(B_13,B_13) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33627,c_135])).

tff(c_33354,plain,(
    ! [A_1669,B_1670] :
      ( r2_hidden('#skF_2'(A_1669,B_1670),k3_xboole_0(A_1669,B_1670))
      | r1_xboole_0(A_1669,B_1670) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_34134,plain,(
    ! [A_1712,B_1713] :
      ( ~ v1_xboole_0(k3_xboole_0(A_1712,B_1713))
      | r1_xboole_0(A_1712,B_1713) ) ),
    inference(resolution,[status(thm)],[c_33354,c_2])).

tff(c_34155,plain,(
    ! [B_1714] :
      ( ~ v1_xboole_0(B_1714)
      | r1_xboole_0(B_1714,B_1714) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_34134])).

tff(c_34166,plain,(
    ! [B_1714] :
      ( k4_xboole_0(B_1714,B_1714) = B_1714
      | ~ v1_xboole_0(B_1714) ) ),
    inference(resolution,[status(thm)],[c_34155,c_30])).

tff(c_34173,plain,(
    ! [B_1714] :
      ( B_1714 = '#skF_3'
      | ~ v1_xboole_0(B_1714) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33655,c_34166])).

tff(c_36347,plain,(
    ! [C_1827] : k2_zfmisc_1('#skF_3',C_1827) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_36337,c_34173])).

tff(c_36351,plain,(
    ! [C_1828] : k2_zfmisc_1('#skF_3',C_1828) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_36337,c_34173])).

tff(c_36371,plain,(
    ! [C_1828,C_28] : k3_zfmisc_1('#skF_3',C_1828,C_28) = k2_zfmisc_1('#skF_3',C_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_36351,c_38])).

tff(c_36388,plain,(
    ! [C_1828,C_28] : k3_zfmisc_1('#skF_3',C_1828,C_28) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36347,c_36371])).

tff(c_33076,plain,(
    r2_hidden('#skF_9',k3_zfmisc_1('#skF_3','#skF_4','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33023,c_24756])).

tff(c_33245,plain,(
    ! [A_1661,A_1662] :
      ( r1_xboole_0(A_1661,A_1662)
      | ~ r1_tarski(A_1661,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_255])).

tff(c_33321,plain,(
    ! [C_1666,A_1667] :
      ( ~ r2_hidden(C_1666,A_1667)
      | ~ r1_tarski(A_1667,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_33245,c_249])).

tff(c_33328,plain,(
    ~ r1_tarski(k3_zfmisc_1('#skF_3','#skF_4','#skF_8'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_33076,c_33321])).

tff(c_33628,plain,(
    ~ r1_tarski(k3_zfmisc_1('#skF_3','#skF_4','#skF_8'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33627,c_33328])).

tff(c_36392,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36388,c_33628])).

tff(c_36400,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_36392])).

tff(c_36402,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_33535])).

tff(c_36842,plain,(
    ! [A_1850,B_1851,C_1852,D_1853] :
      ( k5_mcart_1(A_1850,B_1851,C_1852,D_1853) = k1_mcart_1(k1_mcart_1(D_1853))
      | ~ m1_subset_1(D_1853,k3_zfmisc_1(A_1850,B_1851,C_1852))
      | k1_xboole_0 = C_1852
      | k1_xboole_0 = B_1851
      | k1_xboole_0 = A_1850 ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_36845,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_54,c_36842])).

tff(c_36848,plain,(
    k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_36402,c_24758,c_33065,c_36845])).

tff(c_33293,plain,(
    ! [A_1663,B_1664,C_1665] : k2_zfmisc_1(k2_zfmisc_1(A_1663,B_1664),C_1665) = k3_zfmisc_1(A_1663,B_1664,C_1665) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_39788,plain,(
    ! [A_1972,A_1973,B_1974,C_1975] :
      ( r2_hidden(k1_mcart_1(A_1972),k2_zfmisc_1(A_1973,B_1974))
      | ~ r2_hidden(A_1972,k3_zfmisc_1(A_1973,B_1974,C_1975)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33293,c_42])).

tff(c_39812,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_33076,c_39788])).

tff(c_39820,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_39812,c_42])).

tff(c_39834,plain,(
    r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36848,c_39820])).

tff(c_39836,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33026,c_39834])).

tff(c_39837,plain,(
    '#skF_5' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_575])).

tff(c_40142,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_8','#skF_9'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39837,c_33026])).

tff(c_40146,plain,(
    ! [A_1997,B_1998,C_1999] :
      ( r2_hidden(k1_mcart_1(A_1997),B_1998)
      | ~ r2_hidden(A_1997,k2_zfmisc_1(B_1998,C_1999)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_42276,plain,(
    ! [B_2131,C_2132] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_2131,C_2132))),B_2131)
      | v1_xboole_0(k2_zfmisc_1(B_2131,C_2132)) ) ),
    inference(resolution,[status(thm)],[c_4,c_40146])).

tff(c_39881,plain,(
    ! [A_1980,B_1981] :
      ( r1_tarski(A_1980,B_1981)
      | ~ r1_tarski(A_1980,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_412])).

tff(c_39887,plain,(
    ! [A_14,B_1981] :
      ( r1_tarski(A_14,B_1981)
      | k4_xboole_0(A_14,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_39881])).

tff(c_39897,plain,(
    ! [A_14,B_1981] :
      ( r1_tarski(A_14,B_1981)
      | k1_xboole_0 != A_14 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_39887])).

tff(c_39863,plain,(
    ! [A_1976] :
      ( r1_tarski(A_1976,'#skF_8')
      | k1_xboole_0 != A_1976 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_523])).

tff(c_12,plain,(
    ! [B_13,A_12] :
      ( B_13 = A_12
      | ~ r1_tarski(B_13,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_40471,plain,(
    ! [A_2015] :
      ( A_2015 = '#skF_8'
      | ~ r1_tarski('#skF_8',A_2015)
      | k1_xboole_0 != A_2015 ) ),
    inference(resolution,[status(thm)],[c_39863,c_12])).

tff(c_40484,plain,(
    ! [B_1981] :
      ( B_1981 = '#skF_8'
      | k1_xboole_0 != B_1981
      | k1_xboole_0 != '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_39897,c_40471])).

tff(c_40488,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_40484])).

tff(c_39842,plain,(
    m1_subset_1('#skF_9',k3_zfmisc_1('#skF_3','#skF_4','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39837,c_54])).

tff(c_40516,plain,(
    ! [A_2019,B_2020,C_2021,D_2022] :
      ( k7_mcart_1(A_2019,B_2020,C_2021,D_2022) = k2_mcart_1(D_2022)
      | ~ m1_subset_1(D_2022,k3_zfmisc_1(A_2019,B_2020,C_2021))
      | k1_xboole_0 = C_2021
      | k1_xboole_0 = B_2020
      | k1_xboole_0 = A_2019 ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_40519,plain,
    ( k7_mcart_1('#skF_3','#skF_4','#skF_8','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_39842,c_40516])).

tff(c_40522,plain,
    ( k7_mcart_1('#skF_3','#skF_4','#skF_8','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_24758,c_40488,c_40519])).

tff(c_40547,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_40522])).

tff(c_40572,plain,(
    ! [C_94] : ~ r2_hidden(C_94,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40547,c_503])).

tff(c_42321,plain,(
    ! [C_2133] : v1_xboole_0(k2_zfmisc_1('#skF_3',C_2133)) ),
    inference(resolution,[status(thm)],[c_42276,c_40572])).

tff(c_40305,plain,(
    ! [A_2009,B_2010] :
      ( r2_hidden('#skF_2'(A_2009,B_2010),k3_xboole_0(A_2009,B_2010))
      | r1_xboole_0(A_2009,B_2010) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_40489,plain,(
    ! [A_2016,B_2017] :
      ( ~ v1_xboole_0(k3_xboole_0(A_2016,B_2017))
      | r1_xboole_0(A_2016,B_2017) ) ),
    inference(resolution,[status(thm)],[c_40305,c_2])).

tff(c_40500,plain,(
    ! [B_2018] :
      ( ~ v1_xboole_0(B_2018)
      | r1_xboole_0(B_2018,B_2018) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_40489])).

tff(c_40508,plain,(
    ! [B_2018] :
      ( k4_xboole_0(B_2018,B_2018) = B_2018
      | ~ v1_xboole_0(B_2018) ) ),
    inference(resolution,[status(thm)],[c_40500,c_30])).

tff(c_40514,plain,(
    ! [B_2018] :
      ( k1_xboole_0 = B_2018
      | ~ v1_xboole_0(B_2018) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_40508])).

tff(c_40548,plain,(
    ! [B_2018] :
      ( B_2018 = '#skF_3'
      | ~ v1_xboole_0(B_2018) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40547,c_40514])).

tff(c_42331,plain,(
    ! [C_2133] : k2_zfmisc_1('#skF_3',C_2133) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_42321,c_40548])).

tff(c_42335,plain,(
    ! [C_2134] : k2_zfmisc_1('#skF_3',C_2134) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_42321,c_40548])).

tff(c_42357,plain,(
    ! [C_2134,C_28] : k3_zfmisc_1('#skF_3',C_2134,C_28) = k2_zfmisc_1('#skF_3',C_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_42335,c_38])).

tff(c_42373,plain,(
    ! [C_2134,C_28] : k3_zfmisc_1('#skF_3',C_2134,C_28) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42331,c_42357])).

tff(c_39953,plain,(
    r2_hidden('#skF_9',k3_zfmisc_1('#skF_3','#skF_4','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33023,c_24756])).

tff(c_39980,plain,(
    ! [A_1988,A_1989] :
      ( r1_xboole_0(A_1988,A_1989)
      | ~ r1_tarski(A_1988,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_255])).

tff(c_40154,plain,(
    ! [C_2000,A_2001] :
      ( ~ r2_hidden(C_2000,A_2001)
      | ~ r1_tarski(A_2001,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_39980,c_249])).

tff(c_40161,plain,(
    ~ r1_tarski(k3_zfmisc_1('#skF_3','#skF_4','#skF_8'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_39953,c_40154])).

tff(c_40554,plain,(
    ~ r1_tarski(k3_zfmisc_1('#skF_3','#skF_4','#skF_8'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40547,c_40161])).

tff(c_42376,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42373,c_40554])).

tff(c_42384,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_42376])).

tff(c_42386,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_40522])).

tff(c_42655,plain,(
    ! [A_2147,B_2148,C_2149,D_2150] :
      ( k5_mcart_1(A_2147,B_2148,C_2149,D_2150) = k1_mcart_1(k1_mcart_1(D_2150))
      | ~ m1_subset_1(D_2150,k3_zfmisc_1(A_2147,B_2148,C_2149))
      | k1_xboole_0 = C_2149
      | k1_xboole_0 = B_2148
      | k1_xboole_0 = A_2147 ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_42658,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_8','#skF_9')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_39842,c_42655])).

tff(c_42661,plain,(
    k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_42386,c_24758,c_40488,c_42658])).

tff(c_46751,plain,(
    ! [A_2293,A_2294,B_2295,C_2296] :
      ( r2_hidden(k1_mcart_1(A_2293),k2_zfmisc_1(A_2294,B_2295))
      | ~ r2_hidden(A_2293,k3_zfmisc_1(A_2294,B_2295,C_2296)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_40146])).

tff(c_46775,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_39953,c_46751])).

tff(c_46781,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_46775,c_42])).

tff(c_46795,plain,(
    r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_8','#skF_9'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42661,c_46781])).

tff(c_46797,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40142,c_46795])).

tff(c_46799,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_40484])).

tff(c_46821,plain,(
    ! [C_94] : ~ r2_hidden(C_94,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46799,c_503])).

tff(c_40007,plain,(
    ! [A_1990,B_1991,C_1992] : k2_zfmisc_1(k2_zfmisc_1(A_1990,B_1991),C_1992) = k3_zfmisc_1(A_1990,B_1991,C_1992) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_48756,plain,(
    ! [A_2414,C_2415,A_2416,B_2417] :
      ( r2_hidden(k2_mcart_1(A_2414),C_2415)
      | ~ r2_hidden(A_2414,k3_zfmisc_1(A_2416,B_2417,C_2415)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40007,c_40])).

tff(c_48758,plain,(
    r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_39953,c_48756])).

tff(c_48765,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46821,c_48758])).

tff(c_48766,plain,(
    ! [C_77] : ~ r2_hidden(C_77,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_237])).

tff(c_52479,plain,(
    ! [C_2596] : v1_xboole_0(k2_zfmisc_1('#skF_7',C_2596)) ),
    inference(resolution,[status(thm)],[c_52434,c_48766])).

tff(c_48767,plain,(
    r1_xboole_0('#skF_7','#skF_4') ),
    inference(splitRight,[status(thm)],[c_237])).

tff(c_48779,plain,(
    k4_xboole_0('#skF_7','#skF_4') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_48767,c_30])).

tff(c_195,plain,(
    k4_xboole_0('#skF_7','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_172,c_20])).

tff(c_48797,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48779,c_195])).

tff(c_48812,plain,(
    ! [B_13] : k4_xboole_0(B_13,B_13) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48797,c_135])).

tff(c_49305,plain,(
    ! [A_2458,B_2459] :
      ( r2_hidden('#skF_2'(A_2458,B_2459),k3_xboole_0(A_2458,B_2459))
      | r1_xboole_0(A_2458,B_2459) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_49573,plain,(
    ! [A_2480,B_2481] :
      ( ~ v1_xboole_0(k3_xboole_0(A_2480,B_2481))
      | r1_xboole_0(A_2480,B_2481) ) ),
    inference(resolution,[status(thm)],[c_49305,c_2])).

tff(c_49598,plain,(
    ! [B_2482] :
      ( ~ v1_xboole_0(B_2482)
      | r1_xboole_0(B_2482,B_2482) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_49573])).

tff(c_49606,plain,(
    ! [B_2482] :
      ( k4_xboole_0(B_2482,B_2482) = B_2482
      | ~ v1_xboole_0(B_2482) ) ),
    inference(resolution,[status(thm)],[c_49598,c_30])).

tff(c_49612,plain,(
    ! [B_2482] :
      ( B_2482 = '#skF_7'
      | ~ v1_xboole_0(B_2482) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48812,c_49606])).

tff(c_52486,plain,(
    ! [C_2596] : k2_zfmisc_1('#skF_7',C_2596) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_52479,c_49612])).

tff(c_49070,plain,(
    ! [A_2436,C_2437,B_2438] :
      ( r2_hidden(k2_mcart_1(A_2436),C_2437)
      | ~ r2_hidden(A_2436,k2_zfmisc_1(B_2438,C_2437)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_52280,plain,(
    ! [B_2585,C_2586] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_2585,C_2586))),C_2586)
      | v1_xboole_0(k2_zfmisc_1(B_2585,C_2586)) ) ),
    inference(resolution,[status(thm)],[c_4,c_49070])).

tff(c_52319,plain,(
    ! [B_2587] : v1_xboole_0(k2_zfmisc_1(B_2587,'#skF_7')) ),
    inference(resolution,[status(thm)],[c_52280,c_48766])).

tff(c_52330,plain,(
    ! [B_2588] : k2_zfmisc_1(B_2588,'#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_52319,c_49612])).

tff(c_52340,plain,(
    ! [B_2588,C_28] : k3_zfmisc_1(B_2588,'#skF_7',C_28) = k2_zfmisc_1('#skF_7',C_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_52330,c_38])).

tff(c_52524,plain,(
    ! [B_2588,C_28] : k3_zfmisc_1(B_2588,'#skF_7',C_28) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52486,c_52340])).

tff(c_267,plain,(
    ! [A_78,A_21] :
      ( r1_xboole_0(A_78,A_21)
      | ~ r1_tarski(A_78,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_255])).

tff(c_49133,plain,(
    ! [A_78,A_21] :
      ( r1_xboole_0(A_78,A_21)
      | ~ r1_tarski(A_78,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48797,c_267])).

tff(c_49166,plain,(
    ! [B_2447,C_2448] :
      ( ~ r1_xboole_0(B_2447,B_2447)
      | ~ r2_hidden(C_2448,B_2447) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_234])).

tff(c_49457,plain,(
    ! [C_2468,A_2469] :
      ( ~ r2_hidden(C_2468,A_2469)
      | ~ r1_tarski(A_2469,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_49133,c_49166])).

tff(c_49476,plain,(
    ~ r1_tarski(k3_zfmisc_1('#skF_6','#skF_7','#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_49457])).

tff(c_52525,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52524,c_49476])).

tff(c_52532,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_52525])).

tff(c_52533,plain,
    ( ~ r2_hidden(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_7')
    | ~ r2_hidden(k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_52599,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_52533])).

tff(c_53635,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53554,c_52599])).

tff(c_53316,plain,(
    ! [A_2651,C_2652,B_2653] :
      ( r2_hidden(k2_mcart_1(A_2651),C_2652)
      | ~ r2_hidden(A_2651,k2_zfmisc_1(B_2653,C_2652)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_56209,plain,(
    ! [A_2763,C_2764,A_2765,B_2766] :
      ( r2_hidden(k2_mcart_1(A_2763),C_2764)
      | ~ r2_hidden(A_2763,k3_zfmisc_1(A_2765,B_2766,C_2764)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_53316])).

tff(c_56214,plain,(
    r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_52,c_56209])).

tff(c_56222,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53635,c_56214])).

tff(c_56223,plain,(
    ! [C_2620] : ~ r2_hidden(C_2620,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_52838])).

tff(c_56310,plain,(
    ! [A_2768,C_2769,B_2770] :
      ( r2_hidden(k2_mcart_1(A_2768),C_2769)
      | ~ r2_hidden(A_2768,k2_zfmisc_1(B_2770,C_2769)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_58437,plain,(
    ! [A_2868,C_2869,A_2870,B_2871] :
      ( r2_hidden(k2_mcart_1(A_2868),C_2869)
      | ~ r2_hidden(A_2868,k3_zfmisc_1(A_2870,B_2871,C_2869)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_56310])).

tff(c_58439,plain,(
    r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_52,c_58437])).

tff(c_58446,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56223,c_58439])).

tff(c_58447,plain,(
    ! [C_2620] : ~ r2_hidden(C_2620,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_52841])).

tff(c_52534,plain,(
    r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_58450,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58447,c_52534])).

tff(c_58452,plain,(
    r1_xboole_0('#skF_7','#skF_4') ),
    inference(splitRight,[status(thm)],[c_52835])).

tff(c_58465,plain,(
    k4_xboole_0('#skF_7','#skF_4') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_58452,c_30])).

tff(c_52585,plain,(
    k4_xboole_0('#skF_7','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52562,c_20])).

tff(c_58484,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58465,c_52585])).

tff(c_44,plain,(
    ! [A_32,B_33,C_34,D_36] :
      ( k7_mcart_1(A_32,B_33,C_34,D_36) = k2_mcart_1(D_36)
      | ~ m1_subset_1(D_36,k3_zfmisc_1(A_32,B_33,C_34))
      | k1_xboole_0 = C_34
      | k1_xboole_0 = B_33
      | k1_xboole_0 = A_32 ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_59271,plain,(
    ! [A_2918,B_2919,C_2920,D_2921] :
      ( k7_mcart_1(A_2918,B_2919,C_2920,D_2921) = k2_mcart_1(D_2921)
      | ~ m1_subset_1(D_2921,k3_zfmisc_1(A_2918,B_2919,C_2920))
      | C_2920 = '#skF_7'
      | B_2919 = '#skF_7'
      | A_2918 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58484,c_58484,c_58484,c_44])).

tff(c_59275,plain,
    ( k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') = k2_mcart_1('#skF_9')
    | '#skF_7' = '#skF_5'
    | '#skF_7' = '#skF_4'
    | '#skF_7' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_54,c_59271])).

tff(c_59308,plain,(
    '#skF_7' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_59275])).

tff(c_52577,plain,(
    k4_xboole_0('#skF_6','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52561,c_20])).

tff(c_58538,plain,(
    k4_xboole_0('#skF_6','#skF_3') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58484,c_52577])).

tff(c_58636,plain,(
    ! [A_2878,C_2879,B_2880] :
      ( r1_xboole_0(A_2878,C_2879)
      | ~ r1_tarski(A_2878,k4_xboole_0(B_2880,C_2879)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_59173,plain,(
    ! [A_2912] :
      ( r1_xboole_0(A_2912,'#skF_3')
      | ~ r1_tarski(A_2912,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58538,c_58636])).

tff(c_58459,plain,(
    ~ r1_xboole_0('#skF_6','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_52841])).

tff(c_59186,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_59173,c_58459])).

tff(c_59313,plain,(
    ~ r1_tarski('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59308,c_59186])).

tff(c_59340,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52561,c_59313])).

tff(c_59341,plain,
    ( '#skF_7' = '#skF_4'
    | '#skF_7' = '#skF_5'
    | k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') = k2_mcart_1('#skF_9') ),
    inference(splitRight,[status(thm)],[c_59275])).

tff(c_59511,plain,(
    k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') = k2_mcart_1('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_59341])).

tff(c_60605,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59511,c_52599])).

tff(c_58941,plain,(
    ! [A_2901,B_2902,C_2903] : k2_zfmisc_1(k2_zfmisc_1(A_2901,B_2902),C_2903) = k3_zfmisc_1(A_2901,B_2902,C_2903) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_60766,plain,(
    ! [A_2986,C_2987,A_2988,B_2989] :
      ( r2_hidden(k2_mcart_1(A_2986),C_2987)
      | ~ r2_hidden(A_2986,k3_zfmisc_1(A_2988,B_2989,C_2987)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58941,c_40])).

tff(c_60768,plain,(
    r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_52,c_60766])).

tff(c_60775,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60605,c_60768])).

tff(c_60776,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_7' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_59341])).

tff(c_60778,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_60776])).

tff(c_58504,plain,(
    ! [B_2873,A_2874] :
      ( B_2873 = A_2874
      | ~ r1_tarski(B_2873,A_2874)
      | ~ r1_tarski(A_2874,B_2873) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_58523,plain,
    ( '#skF_7' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_7') ),
    inference(resolution,[status(thm)],[c_52562,c_58504])).

tff(c_58688,plain,(
    ~ r1_tarski('#skF_4','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_58523])).

tff(c_60802,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60778,c_58688])).

tff(c_60818,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_60802])).

tff(c_60820,plain,(
    '#skF_7' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_60776])).

tff(c_59342,plain,(
    '#skF_7' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_59275])).

tff(c_48,plain,(
    ! [A_32,B_33,C_34,D_36] :
      ( k5_mcart_1(A_32,B_33,C_34,D_36) = k1_mcart_1(k1_mcart_1(D_36))
      | ~ m1_subset_1(D_36,k3_zfmisc_1(A_32,B_33,C_34))
      | k1_xboole_0 = C_34
      | k1_xboole_0 = B_33
      | k1_xboole_0 = A_32 ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_59344,plain,(
    ! [A_2925,B_2926,C_2927,D_2928] :
      ( k5_mcart_1(A_2925,B_2926,C_2927,D_2928) = k1_mcart_1(k1_mcart_1(D_2928))
      | ~ m1_subset_1(D_2928,k3_zfmisc_1(A_2925,B_2926,C_2927))
      | C_2927 = '#skF_7'
      | B_2926 = '#skF_7'
      | A_2925 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58484,c_58484,c_58484,c_48])).

tff(c_59347,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | '#skF_7' = '#skF_5'
    | '#skF_7' = '#skF_4'
    | '#skF_7' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_54,c_59344])).

tff(c_59350,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | '#skF_7' = '#skF_5'
    | '#skF_7' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_59342,c_59347])).

tff(c_60821,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | '#skF_7' = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_60820,c_59350])).

tff(c_60822,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_60821])).

tff(c_52629,plain,(
    ! [A_2605,B_2606,C_2607] :
      ( r1_tarski(A_2605,B_2606)
      | ~ r1_tarski(A_2605,k4_xboole_0(B_2606,C_2607)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_52661,plain,(
    ! [B_2608,C_2609] : r1_tarski(k4_xboole_0(B_2608,C_2609),B_2608) ),
    inference(resolution,[status(thm)],[c_16,c_52629])).

tff(c_52688,plain,(
    ! [B_2608,C_2609] : k4_xboole_0(k4_xboole_0(B_2608,C_2609),B_2608) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52661,c_20])).

tff(c_59032,plain,(
    ! [B_2906,C_2907] : k4_xboole_0(k4_xboole_0(B_2906,C_2907),B_2906) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58484,c_52688])).

tff(c_22,plain,(
    ! [A_16,C_18,B_17] :
      ( r1_xboole_0(A_16,C_18)
      | ~ r1_tarski(A_16,k4_xboole_0(B_17,C_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_59250,plain,(
    ! [A_2916,B_2917] :
      ( r1_xboole_0(A_2916,B_2917)
      | ~ r1_tarski(A_2916,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59032,c_22])).

tff(c_59288,plain,(
    ! [B_2923,A_2924] :
      ( r1_xboole_0(B_2923,A_2924)
      | ~ r1_tarski(A_2924,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_59250,c_6])).

tff(c_58931,plain,(
    ~ r1_xboole_0('#skF_8','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_52838])).

tff(c_59303,plain,(
    ~ r1_tarski('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_59288,c_58931])).

tff(c_60832,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60822,c_59303])).

tff(c_60863,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_60832])).

tff(c_60865,plain,(
    '#skF_7' != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_60821])).

tff(c_60819,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_60776])).

tff(c_60866,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60865,c_60819])).

tff(c_60867,plain,(
    ! [C_2620] : ~ r2_hidden(C_2620,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_52838])).

tff(c_60868,plain,(
    r1_xboole_0('#skF_8','#skF_5') ),
    inference(splitRight,[status(thm)],[c_52838])).

tff(c_60899,plain,(
    k4_xboole_0('#skF_8','#skF_5') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_60868,c_30])).

tff(c_52569,plain,(
    k4_xboole_0('#skF_8','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52560,c_20])).

tff(c_58537,plain,(
    k4_xboole_0('#skF_8','#skF_5') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58484,c_52569])).

tff(c_60909,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60899,c_58537])).

tff(c_60953,plain,(
    r2_hidden('#skF_9',k3_zfmisc_1('#skF_6','#skF_8','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60909,c_52])).

tff(c_60875,plain,(
    ! [A_2991,B_2992,C_2993] : k2_zfmisc_1(k2_zfmisc_1(A_2991,B_2992),C_2993) = k3_zfmisc_1(A_2991,B_2992,C_2993) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_62364,plain,(
    ! [A_3063,C_3064,A_3065,B_3066] :
      ( r2_hidden(k2_mcart_1(A_3063),C_3064)
      | ~ r2_hidden(A_3063,k3_zfmisc_1(A_3065,B_3066,C_3064)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60875,c_40])).

tff(c_62366,plain,(
    r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_60953,c_62364])).

tff(c_62373,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60867,c_62366])).

tff(c_62374,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_58523])).

tff(c_58451,plain,(
    ! [C_2620] : ~ r2_hidden(C_2620,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_52835])).

tff(c_62387,plain,(
    ! [C_2620] : ~ r2_hidden(C_2620,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62374,c_58451])).

tff(c_62646,plain,(
    ! [A_3081,C_3082,B_3083] :
      ( r2_hidden(k2_mcart_1(A_3081),C_3082)
      | ~ r2_hidden(A_3081,k2_zfmisc_1(B_3083,C_3082)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_64905,plain,(
    ! [B_3189,C_3190] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_3189,C_3190))),C_3190)
      | v1_xboole_0(k2_zfmisc_1(B_3189,C_3190)) ) ),
    inference(resolution,[status(thm)],[c_4,c_62646])).

tff(c_58540,plain,(
    ! [B_13] : k4_xboole_0(B_13,B_13) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58484,c_135])).

tff(c_62378,plain,(
    ! [B_13] : k4_xboole_0(B_13,B_13) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62374,c_58540])).

tff(c_62779,plain,(
    ! [B_3091,C_3092] :
      ( ~ r1_xboole_0(B_3091,B_3091)
      | ~ r2_hidden(C_3092,B_3091) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_52832])).

tff(c_62788,plain,(
    ! [C_3092,A_63] :
      ( ~ r2_hidden(C_3092,A_63)
      | k4_xboole_0(A_63,A_63) != A_63 ) ),
    inference(resolution,[status(thm)],[c_123,c_62779])).

tff(c_62795,plain,(
    ! [C_3092,A_63] :
      ( ~ r2_hidden(C_3092,A_63)
      | A_63 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62378,c_62788])).

tff(c_65058,plain,(
    ! [C_3200,B_3201] :
      ( C_3200 != '#skF_4'
      | v1_xboole_0(k2_zfmisc_1(B_3201,C_3200)) ) ),
    inference(resolution,[status(thm)],[c_64905,c_62795])).

tff(c_62740,plain,(
    ! [A_3089,B_3090] :
      ( r2_hidden('#skF_2'(A_3089,B_3090),k3_xboole_0(A_3089,B_3090))
      | r1_xboole_0(A_3089,B_3090) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_63112,plain,(
    ! [A_3119,B_3120] :
      ( ~ v1_xboole_0(k3_xboole_0(A_3119,B_3120))
      | r1_xboole_0(A_3119,B_3120) ) ),
    inference(resolution,[status(thm)],[c_62740,c_2])).

tff(c_63133,plain,(
    ! [B_3121] :
      ( ~ v1_xboole_0(B_3121)
      | r1_xboole_0(B_3121,B_3121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_63112])).

tff(c_63138,plain,(
    ! [B_3121] :
      ( k4_xboole_0(B_3121,B_3121) = B_3121
      | ~ v1_xboole_0(B_3121) ) ),
    inference(resolution,[status(thm)],[c_63133,c_30])).

tff(c_63143,plain,(
    ! [B_3121] :
      ( B_3121 = '#skF_4'
      | ~ v1_xboole_0(B_3121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62378,c_63138])).

tff(c_65274,plain,(
    ! [B_3201] : k2_zfmisc_1(B_3201,'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_65058,c_63143])).

tff(c_62389,plain,(
    r2_hidden('#skF_9',k3_zfmisc_1('#skF_6','#skF_4','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62374,c_52])).

tff(c_62565,plain,(
    ! [A_3077,B_3078,C_3079] :
      ( r2_hidden(k1_mcart_1(A_3077),B_3078)
      | ~ r2_hidden(A_3077,k2_zfmisc_1(B_3078,C_3079)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_65330,plain,(
    ! [A_3218,A_3219,B_3220,C_3221] :
      ( r2_hidden(k1_mcart_1(A_3218),k2_zfmisc_1(A_3219,B_3220))
      | ~ r2_hidden(A_3218,k3_zfmisc_1(A_3219,B_3220,C_3221)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_62565])).

tff(c_65342,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k2_zfmisc_1('#skF_6','#skF_4')) ),
    inference(resolution,[status(thm)],[c_62389,c_65330])).

tff(c_65351,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65274,c_65342])).

tff(c_65353,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62387,c_65351])).

tff(c_65354,plain,(
    ! [C_2620] : ~ r2_hidden(C_2620,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_52841])).

tff(c_65364,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65354,c_52534])).

tff(c_65365,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_52533])).

tff(c_65579,plain,(
    ! [A_3238,C_3239,B_3240] :
      ( r1_xboole_0(A_3238,C_3239)
      | ~ r1_tarski(A_3238,k4_xboole_0(B_3240,C_3239)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_65623,plain,(
    ! [C_3241] : r1_xboole_0(k1_xboole_0,C_3241) ),
    inference(resolution,[status(thm)],[c_28,c_65579])).

tff(c_65632,plain,(
    ! [C_3242] : r1_xboole_0(C_3242,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_65623,c_6])).

tff(c_65638,plain,(
    ! [C_3242] : k4_xboole_0(C_3242,k1_xboole_0) = C_3242 ),
    inference(resolution,[status(thm)],[c_65632,c_30])).

tff(c_65785,plain,(
    ! [A_3249,A_3250] :
      ( r1_xboole_0(A_3249,A_3250)
      | ~ r1_tarski(A_3249,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_65579])).

tff(c_66154,plain,(
    ! [A_3274,A_3275] :
      ( r1_xboole_0(A_3274,A_3275)
      | ~ r1_tarski(A_3275,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_65785,c_6])).

tff(c_65793,plain,(
    ! [A_3251,B_3252,C_3253] :
      ( ~ r1_xboole_0(A_3251,B_3252)
      | ~ r2_hidden(C_3253,k3_xboole_0(A_3251,B_3252)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_65802,plain,(
    ! [C_3253] :
      ( ~ r1_xboole_0('#skF_6','#skF_3')
      | ~ r2_hidden(C_3253,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52578,c_65793])).

tff(c_66056,plain,(
    ~ r1_xboole_0('#skF_6','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_65802])).

tff(c_66169,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_66154,c_66056])).

tff(c_66183,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_66169])).

tff(c_66185,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65638,c_66183])).

tff(c_65796,plain,(
    ! [C_3253] :
      ( ~ r1_xboole_0('#skF_7','#skF_4')
      | ~ r2_hidden(C_3253,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52586,c_65793])).

tff(c_65967,plain,(
    ~ r1_xboole_0('#skF_7','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_65796])).

tff(c_66170,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_66154,c_65967])).

tff(c_66188,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_66170])).

tff(c_66190,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65638,c_66188])).

tff(c_65792,plain,(
    ! [A_3250,A_3249] :
      ( r1_xboole_0(A_3250,A_3249)
      | ~ r1_tarski(A_3249,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_65785,c_6])).

tff(c_65799,plain,(
    ! [C_3253] :
      ( ~ r1_xboole_0('#skF_8','#skF_5')
      | ~ r2_hidden(C_3253,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52570,c_65793])).

tff(c_66191,plain,(
    ~ r1_xboole_0('#skF_8','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_65799])).

tff(c_66204,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_65792,c_66191])).

tff(c_66211,plain,(
    k4_xboole_0('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_66204])).

tff(c_66213,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65638,c_66211])).

tff(c_67169,plain,(
    ! [A_3318,B_3319,C_3320,D_3321] :
      ( k6_mcart_1(A_3318,B_3319,C_3320,D_3321) = k2_mcart_1(k1_mcart_1(D_3321))
      | ~ m1_subset_1(D_3321,k3_zfmisc_1(A_3318,B_3319,C_3320))
      | k1_xboole_0 = C_3320
      | k1_xboole_0 = B_3319
      | k1_xboole_0 = A_3318 ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_67172,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_9')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_54,c_67169])).

tff(c_67175,plain,(
    k2_mcart_1(k1_mcart_1('#skF_9')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_66185,c_66190,c_66213,c_67172])).

tff(c_66003,plain,(
    ! [A_3268,B_3269,C_3270] :
      ( r2_hidden(k1_mcart_1(A_3268),B_3269)
      | ~ r2_hidden(A_3268,k2_zfmisc_1(B_3269,C_3270)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_70585,plain,(
    ! [A_3453,A_3454,B_3455,C_3456] :
      ( r2_hidden(k1_mcart_1(A_3453),k2_zfmisc_1(A_3454,B_3455))
      | ~ r2_hidden(A_3453,k3_zfmisc_1(A_3454,B_3455,C_3456)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_66003])).

tff(c_70616,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_52,c_70585])).

tff(c_70619,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_70616,c_40])).

tff(c_70638,plain,(
    r2_hidden(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67175,c_70619])).

tff(c_70640,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65365,c_70638])).

tff(c_70641,plain,(
    ! [C_3253] : ~ r2_hidden(C_3253,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_65799])).

tff(c_65366,plain,(
    r2_hidden(k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_52533])).

tff(c_70644,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70641,c_65366])).

tff(c_70645,plain,(
    ! [C_3253] : ~ r2_hidden(C_3253,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_65802])).

tff(c_70649,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70645,c_52534])).

tff(c_70650,plain,(
    ! [C_3253] : ~ r2_hidden(C_3253,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_65796])).

tff(c_70651,plain,(
    r1_xboole_0('#skF_7','#skF_4') ),
    inference(splitRight,[status(thm)],[c_65796])).

tff(c_70663,plain,(
    k4_xboole_0('#skF_7','#skF_4') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_70651,c_30])).

tff(c_70680,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70663,c_52585])).

tff(c_32,plain,(
    ! [A_22,B_23] :
      ( r1_xboole_0(A_22,B_23)
      | k4_xboole_0(A_22,B_23) != A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_65822,plain,(
    ! [B_3255,C_3256] :
      ( ~ r1_xboole_0(B_3255,B_3255)
      | ~ r2_hidden(C_3256,B_3255) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_65793])).

tff(c_65837,plain,(
    ! [C_3256,B_23] :
      ( ~ r2_hidden(C_3256,B_23)
      | k4_xboole_0(B_23,B_23) != B_23 ) ),
    inference(resolution,[status(thm)],[c_32,c_65822])).

tff(c_65846,plain,(
    ! [C_3257,B_3258] :
      ( ~ r2_hidden(C_3257,B_3258)
      | k1_xboole_0 != B_3258 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_65837])).

tff(c_65862,plain,(
    ! [A_1] :
      ( k1_xboole_0 != A_1
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_65846])).

tff(c_70716,plain,(
    ! [A_1] :
      ( A_1 != '#skF_7'
      | v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70680,c_65862])).

tff(c_70787,plain,(
    ! [A_3464,C_3465,B_3466] :
      ( r2_hidden(k2_mcart_1(A_3464),C_3465)
      | ~ r2_hidden(A_3464,k2_zfmisc_1(B_3466,C_3465)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_73487,plain,(
    ! [B_3592,C_3593] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_3592,C_3593))),C_3593)
      | v1_xboole_0(k2_zfmisc_1(B_3592,C_3593)) ) ),
    inference(resolution,[status(thm)],[c_4,c_70787])).

tff(c_73596,plain,(
    ! [C_3600,B_3601] :
      ( ~ v1_xboole_0(C_3600)
      | v1_xboole_0(k2_zfmisc_1(B_3601,C_3600)) ) ),
    inference(resolution,[status(thm)],[c_73487,c_2])).

tff(c_70730,plain,(
    ! [B_13] : k4_xboole_0(B_13,B_13) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70680,c_135])).

tff(c_71010,plain,(
    ! [A_3472,B_3473] :
      ( r2_hidden('#skF_2'(A_3472,B_3473),k3_xboole_0(A_3472,B_3473))
      | r1_xboole_0(A_3472,B_3473) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_71486,plain,(
    ! [A_3506,B_3507] :
      ( ~ v1_xboole_0(k3_xboole_0(A_3506,B_3507))
      | r1_xboole_0(A_3506,B_3507) ) ),
    inference(resolution,[status(thm)],[c_71010,c_2])).

tff(c_71507,plain,(
    ! [B_3508] :
      ( ~ v1_xboole_0(B_3508)
      | r1_xboole_0(B_3508,B_3508) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_71486])).

tff(c_71512,plain,(
    ! [B_3508] :
      ( k4_xboole_0(B_3508,B_3508) = B_3508
      | ~ v1_xboole_0(B_3508) ) ),
    inference(resolution,[status(thm)],[c_71507,c_30])).

tff(c_71517,plain,(
    ! [B_3508] :
      ( B_3508 = '#skF_7'
      | ~ v1_xboole_0(B_3508) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70730,c_71512])).

tff(c_73623,plain,(
    ! [B_3604,C_3605] :
      ( k2_zfmisc_1(B_3604,C_3605) = '#skF_7'
      | ~ v1_xboole_0(C_3605) ) ),
    inference(resolution,[status(thm)],[c_73596,c_71517])).

tff(c_73836,plain,(
    ! [B_3604] : k2_zfmisc_1(B_3604,'#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_70716,c_73623])).

tff(c_70673,plain,(
    ! [A_3458,B_3459,C_3460] :
      ( r2_hidden(k1_mcart_1(A_3458),B_3459)
      | ~ r2_hidden(A_3458,k2_zfmisc_1(B_3459,C_3460)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_73892,plain,(
    ! [A_3620,A_3621,B_3622,C_3623] :
      ( r2_hidden(k1_mcart_1(A_3620),k2_zfmisc_1(A_3621,B_3622))
      | ~ r2_hidden(A_3620,k3_zfmisc_1(A_3621,B_3622,C_3623)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_70673])).

tff(c_73904,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_52,c_73892])).

tff(c_73913,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73836,c_73904])).

tff(c_73915,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70650,c_73913])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n025.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:57:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.85/6.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.42/6.26  
% 13.42/6.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.42/6.26  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2
% 13.42/6.26  
% 13.42/6.26  %Foreground sorts:
% 13.42/6.26  
% 13.42/6.26  
% 13.42/6.26  %Background operators:
% 13.42/6.26  
% 13.42/6.26  
% 13.42/6.26  %Foreground operators:
% 13.42/6.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.42/6.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.42/6.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.42/6.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 13.42/6.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.42/6.26  tff('#skF_7', type, '#skF_7': $i).
% 13.42/6.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.42/6.26  tff('#skF_5', type, '#skF_5': $i).
% 13.42/6.26  tff('#skF_6', type, '#skF_6': $i).
% 13.42/6.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 13.42/6.26  tff('#skF_3', type, '#skF_3': $i).
% 13.42/6.26  tff('#skF_9', type, '#skF_9': $i).
% 13.42/6.26  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 13.42/6.26  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 13.42/6.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.42/6.26  tff('#skF_8', type, '#skF_8': $i).
% 13.42/6.26  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 13.42/6.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.42/6.26  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 13.42/6.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.42/6.26  tff('#skF_4', type, '#skF_4': $i).
% 13.42/6.26  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 13.42/6.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.42/6.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 13.42/6.26  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 13.42/6.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.42/6.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.42/6.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.42/6.26  
% 13.64/6.31  tff(f_55, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.64/6.31  tff(f_127, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (![F]: (m1_subset_1(F, k1_zfmisc_1(C)) => (![G]: (m1_subset_1(G, k3_zfmisc_1(A, B, C)) => (r2_hidden(G, k3_zfmisc_1(D, E, F)) => ((r2_hidden(k5_mcart_1(A, B, C, G), D) & r2_hidden(k6_mcart_1(A, B, C, G), E)) & r2_hidden(k7_mcart_1(A, B, C, G), F))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_mcart_1)).
% 13.64/6.31  tff(f_79, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 13.64/6.31  tff(f_71, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 13.64/6.31  tff(f_65, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 13.64/6.31  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 13.64/6.31  tff(f_75, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 13.64/6.31  tff(f_59, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 13.64/6.31  tff(f_69, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 13.64/6.31  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 13.64/6.31  tff(f_107, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 13.64/6.31  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 13.64/6.31  tff(f_87, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 13.64/6.31  tff(f_81, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 13.64/6.31  tff(c_16, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.64/6.31  tff(c_60, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.64/6.31  tff(c_52550, plain, (![A_2599, B_2600]: (r1_tarski(A_2599, B_2600) | ~m1_subset_1(A_2599, k1_zfmisc_1(B_2600)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 13.64/6.31  tff(c_52561, plain, (r1_tarski('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_52550])).
% 13.64/6.31  tff(c_54, plain, (m1_subset_1('#skF_9', k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.64/6.31  tff(c_28, plain, (![A_21]: (r1_tarski(k1_xboole_0, A_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.64/6.31  tff(c_52974, plain, (![A_2630, C_2631, B_2632]: (r1_xboole_0(A_2630, C_2631) | ~r1_tarski(A_2630, k4_xboole_0(B_2632, C_2631)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.64/6.31  tff(c_53018, plain, (![C_2633]: (r1_xboole_0(k1_xboole_0, C_2633))), inference(resolution, [status(thm)], [c_28, c_52974])).
% 13.64/6.31  tff(c_6, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.64/6.31  tff(c_53031, plain, (![C_2634]: (r1_xboole_0(C_2634, k1_xboole_0))), inference(resolution, [status(thm)], [c_53018, c_6])).
% 13.64/6.31  tff(c_30, plain, (![A_22, B_23]: (k4_xboole_0(A_22, B_23)=A_22 | ~r1_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.64/6.31  tff(c_53041, plain, (![C_2634]: (k4_xboole_0(C_2634, k1_xboole_0)=C_2634)), inference(resolution, [status(thm)], [c_53031, c_30])).
% 13.64/6.31  tff(c_18, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | k4_xboole_0(A_14, B_15)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.64/6.31  tff(c_124, plain, (![A_65, B_66]: (k4_xboole_0(A_65, B_66)=k1_xboole_0 | ~r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.64/6.31  tff(c_136, plain, (![A_21]: (k4_xboole_0(k1_xboole_0, A_21)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_124])).
% 13.64/6.31  tff(c_53190, plain, (![A_2643, A_2644]: (r1_xboole_0(A_2643, A_2644) | ~r1_tarski(A_2643, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_136, c_52974])).
% 13.64/6.31  tff(c_53323, plain, (![A_2654, A_2655]: (r1_xboole_0(A_2654, A_2655) | ~r1_tarski(A_2655, k1_xboole_0))), inference(resolution, [status(thm)], [c_53190, c_6])).
% 13.64/6.31  tff(c_26, plain, (![A_19, B_20]: (k3_xboole_0(A_19, B_20)=A_19 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_69])).
% 13.64/6.31  tff(c_52578, plain, (k3_xboole_0('#skF_6', '#skF_3')='#skF_6'), inference(resolution, [status(thm)], [c_52561, c_26])).
% 13.64/6.31  tff(c_52832, plain, (![A_2618, B_2619, C_2620]: (~r1_xboole_0(A_2618, B_2619) | ~r2_hidden(C_2620, k3_xboole_0(A_2618, B_2619)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.64/6.31  tff(c_52841, plain, (![C_2620]: (~r1_xboole_0('#skF_6', '#skF_3') | ~r2_hidden(C_2620, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_52578, c_52832])).
% 13.64/6.31  tff(c_53206, plain, (~r1_xboole_0('#skF_6', '#skF_3')), inference(splitLeft, [status(thm)], [c_52841])).
% 13.64/6.31  tff(c_53342, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_53323, c_53206])).
% 13.64/6.31  tff(c_53354, plain, (k4_xboole_0('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_53342])).
% 13.64/6.31  tff(c_53356, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_53041, c_53354])).
% 13.64/6.31  tff(c_58, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.64/6.31  tff(c_52562, plain, (r1_tarski('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_52550])).
% 13.64/6.31  tff(c_52586, plain, (k3_xboole_0('#skF_7', '#skF_4')='#skF_7'), inference(resolution, [status(thm)], [c_52562, c_26])).
% 13.64/6.31  tff(c_52835, plain, (![C_2620]: (~r1_xboole_0('#skF_7', '#skF_4') | ~r2_hidden(C_2620, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_52586, c_52832])).
% 13.64/6.31  tff(c_52860, plain, (~r1_xboole_0('#skF_7', '#skF_4')), inference(splitLeft, [status(thm)], [c_52835])).
% 13.64/6.31  tff(c_53344, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_53323, c_52860])).
% 13.64/6.31  tff(c_53359, plain, (k4_xboole_0('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_53344])).
% 13.64/6.31  tff(c_53361, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_53041, c_53359])).
% 13.64/6.31  tff(c_56, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.64/6.31  tff(c_52560, plain, (r1_tarski('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_56, c_52550])).
% 13.64/6.31  tff(c_52570, plain, (k3_xboole_0('#skF_8', '#skF_5')='#skF_8'), inference(resolution, [status(thm)], [c_52560, c_26])).
% 13.64/6.31  tff(c_52838, plain, (![C_2620]: (~r1_xboole_0('#skF_8', '#skF_5') | ~r2_hidden(C_2620, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_52570, c_52832])).
% 13.64/6.31  tff(c_53297, plain, (~r1_xboole_0('#skF_8', '#skF_5')), inference(splitLeft, [status(thm)], [c_52838])).
% 13.64/6.31  tff(c_53341, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_53323, c_53297])).
% 13.64/6.31  tff(c_53349, plain, (k4_xboole_0('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_53341])).
% 13.64/6.31  tff(c_53351, plain, (k1_xboole_0!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_53041, c_53349])).
% 13.64/6.31  tff(c_53548, plain, (![A_2662, B_2663, C_2664, D_2665]: (k7_mcart_1(A_2662, B_2663, C_2664, D_2665)=k2_mcart_1(D_2665) | ~m1_subset_1(D_2665, k3_zfmisc_1(A_2662, B_2663, C_2664)) | k1_xboole_0=C_2664 | k1_xboole_0=B_2663 | k1_xboole_0=A_2662)), inference(cnfTransformation, [status(thm)], [f_107])).
% 13.64/6.31  tff(c_53551, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_54, c_53548])).
% 13.64/6.31  tff(c_53554, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')=k2_mcart_1('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_53356, c_53361, c_53351, c_53551])).
% 13.64/6.31  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.64/6.31  tff(c_49207, plain, (![A_2452, B_2453, C_2454]: (r2_hidden(k1_mcart_1(A_2452), B_2453) | ~r2_hidden(A_2452, k2_zfmisc_1(B_2453, C_2454)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.64/6.31  tff(c_52434, plain, (![B_2594, C_2595]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_2594, C_2595))), B_2594) | v1_xboole_0(k2_zfmisc_1(B_2594, C_2595)))), inference(resolution, [status(thm)], [c_4, c_49207])).
% 13.64/6.31  tff(c_50, plain, (~r2_hidden(k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_8') | ~r2_hidden(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_7') | ~r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.64/6.31  tff(c_144, plain, (~r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_6')), inference(splitLeft, [status(thm)], [c_50])).
% 13.64/6.31  tff(c_255, plain, (![A_78, C_79, B_80]: (r1_xboole_0(A_78, C_79) | ~r1_tarski(A_78, k4_xboole_0(B_80, C_79)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.64/6.31  tff(c_286, plain, (![C_81]: (r1_xboole_0(k1_xboole_0, C_81))), inference(resolution, [status(thm)], [c_28, c_255])).
% 13.64/6.31  tff(c_295, plain, (![C_82]: (r1_xboole_0(C_82, k1_xboole_0))), inference(resolution, [status(thm)], [c_286, c_6])).
% 13.64/6.31  tff(c_301, plain, (![C_82]: (k4_xboole_0(C_82, k1_xboole_0)=C_82)), inference(resolution, [status(thm)], [c_295, c_30])).
% 13.64/6.31  tff(c_135, plain, (![B_13]: (k4_xboole_0(B_13, B_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_124])).
% 13.64/6.31  tff(c_412, plain, (![A_88, B_89, C_90]: (r1_tarski(A_88, B_89) | ~r1_tarski(A_88, k4_xboole_0(B_89, C_90)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.64/6.31  tff(c_24930, plain, (![A_1227, B_1228]: (r1_tarski(A_1227, B_1228) | ~r1_tarski(A_1227, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_135, c_412])).
% 13.64/6.31  tff(c_24936, plain, (![A_14, B_1228]: (r1_tarski(A_14, B_1228) | k4_xboole_0(A_14, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_24930])).
% 13.64/6.31  tff(c_24953, plain, (![A_1229, B_1230]: (r1_tarski(A_1229, B_1230) | k1_xboole_0!=A_1229)), inference(demodulation, [status(thm), theory('equality')], [c_301, c_24936])).
% 13.64/6.31  tff(c_160, plain, (![A_69, B_70]: (r1_tarski(A_69, B_70) | ~m1_subset_1(A_69, k1_zfmisc_1(B_70)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 13.64/6.31  tff(c_171, plain, (r1_tarski('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_160])).
% 13.64/6.31  tff(c_557, plain, (![B_100, A_101]: (B_100=A_101 | ~r1_tarski(B_100, A_101) | ~r1_tarski(A_101, B_100))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.64/6.31  tff(c_574, plain, ('#skF_6'='#skF_3' | ~r1_tarski('#skF_3', '#skF_6')), inference(resolution, [status(thm)], [c_171, c_557])).
% 13.64/6.31  tff(c_24782, plain, (~r1_tarski('#skF_3', '#skF_6')), inference(splitLeft, [status(thm)], [c_574])).
% 13.64/6.31  tff(c_24989, plain, (k1_xboole_0!='#skF_3'), inference(resolution, [status(thm)], [c_24953, c_24782])).
% 13.64/6.31  tff(c_749, plain, (![A_114, B_115]: (r1_tarski(A_114, B_115) | ~r1_tarski(A_114, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_135, c_412])).
% 13.64/6.31  tff(c_755, plain, (![A_14, B_115]: (r1_tarski(A_14, B_115) | k4_xboole_0(A_14, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_749])).
% 13.64/6.31  tff(c_772, plain, (![A_116, B_117]: (r1_tarski(A_116, B_117) | k1_xboole_0!=A_116)), inference(demodulation, [status(thm), theory('equality')], [c_301, c_755])).
% 13.64/6.31  tff(c_612, plain, (~r1_tarski('#skF_3', '#skF_6')), inference(splitLeft, [status(thm)], [c_574])).
% 13.64/6.31  tff(c_811, plain, (k1_xboole_0!='#skF_3'), inference(resolution, [status(thm)], [c_772, c_612])).
% 13.64/6.31  tff(c_172, plain, (r1_tarski('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_160])).
% 13.64/6.31  tff(c_573, plain, ('#skF_7'='#skF_4' | ~r1_tarski('#skF_4', '#skF_7')), inference(resolution, [status(thm)], [c_172, c_557])).
% 13.64/6.31  tff(c_607, plain, (~r1_tarski('#skF_4', '#skF_7')), inference(splitLeft, [status(thm)], [c_573])).
% 13.64/6.31  tff(c_812, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_772, c_607])).
% 13.64/6.31  tff(c_170, plain, (r1_tarski('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_56, c_160])).
% 13.64/6.31  tff(c_20, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=k1_xboole_0 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.64/6.31  tff(c_179, plain, (k4_xboole_0('#skF_8', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_170, c_20])).
% 13.64/6.31  tff(c_515, plain, (![A_96]: (r1_tarski(A_96, '#skF_8') | ~r1_tarski(A_96, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_179, c_412])).
% 13.64/6.31  tff(c_523, plain, (![A_14]: (r1_tarski(A_14, '#skF_8') | k4_xboole_0(A_14, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_515])).
% 13.64/6.31  tff(c_628, plain, (![A_106]: (r1_tarski(A_106, '#skF_8') | k1_xboole_0!=A_106)), inference(demodulation, [status(thm), theory('equality')], [c_301, c_523])).
% 13.64/6.31  tff(c_575, plain, ('#skF_5'='#skF_8' | ~r1_tarski('#skF_5', '#skF_8')), inference(resolution, [status(thm)], [c_170, c_557])).
% 13.64/6.31  tff(c_617, plain, (~r1_tarski('#skF_5', '#skF_8')), inference(splitLeft, [status(thm)], [c_575])).
% 13.64/6.31  tff(c_640, plain, (k1_xboole_0!='#skF_5'), inference(resolution, [status(thm)], [c_628, c_617])).
% 13.64/6.31  tff(c_1277, plain, (![A_140, B_141, C_142, D_143]: (k5_mcart_1(A_140, B_141, C_142, D_143)=k1_mcart_1(k1_mcart_1(D_143)) | ~m1_subset_1(D_143, k3_zfmisc_1(A_140, B_141, C_142)) | k1_xboole_0=C_142 | k1_xboole_0=B_141 | k1_xboole_0=A_140)), inference(cnfTransformation, [status(thm)], [f_107])).
% 13.64/6.31  tff(c_1280, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_54, c_1277])).
% 13.64/6.31  tff(c_1283, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_811, c_812, c_640, c_1280])).
% 13.64/6.31  tff(c_52, plain, (r2_hidden('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.64/6.31  tff(c_38, plain, (![A_26, B_27, C_28]: (k2_zfmisc_1(k2_zfmisc_1(A_26, B_27), C_28)=k3_zfmisc_1(A_26, B_27, C_28))), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.64/6.31  tff(c_842, plain, (![A_118, B_119, C_120]: (r2_hidden(k1_mcart_1(A_118), B_119) | ~r2_hidden(A_118, k2_zfmisc_1(B_119, C_120)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.64/6.31  tff(c_4017, plain, (![A_265, A_266, B_267, C_268]: (r2_hidden(k1_mcart_1(A_265), k2_zfmisc_1(A_266, B_267)) | ~r2_hidden(A_265, k3_zfmisc_1(A_266, B_267, C_268)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_842])).
% 13.64/6.31  tff(c_4045, plain, (r2_hidden(k1_mcart_1('#skF_9'), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_52, c_4017])).
% 13.64/6.31  tff(c_42, plain, (![A_29, B_30, C_31]: (r2_hidden(k1_mcart_1(A_29), B_30) | ~r2_hidden(A_29, k2_zfmisc_1(B_30, C_31)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.64/6.31  tff(c_4051, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')), '#skF_6')), inference(resolution, [status(thm)], [c_4045, c_42])).
% 13.64/6.31  tff(c_4065, plain, (r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1283, c_4051])).
% 13.64/6.31  tff(c_4067, plain, $false, inference(negUnitSimplification, [status(thm)], [c_144, c_4065])).
% 13.64/6.31  tff(c_4068, plain, ('#skF_5'='#skF_8'), inference(splitRight, [status(thm)], [c_575])).
% 13.64/6.31  tff(c_4071, plain, (~r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_8', '#skF_9'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4068, c_144])).
% 13.64/6.31  tff(c_4192, plain, (![A_277, B_278]: (r1_tarski(A_277, B_278) | ~r1_tarski(A_277, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_135, c_412])).
% 13.64/6.31  tff(c_4198, plain, (![A_14, B_278]: (r1_tarski(A_14, B_278) | k4_xboole_0(A_14, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_4192])).
% 13.64/6.31  tff(c_4215, plain, (![A_279, B_280]: (r1_tarski(A_279, B_280) | k1_xboole_0!=A_279)), inference(demodulation, [status(thm), theory('equality')], [c_301, c_4198])).
% 13.64/6.31  tff(c_4250, plain, (k1_xboole_0!='#skF_3'), inference(resolution, [status(thm)], [c_4215, c_612])).
% 13.64/6.31  tff(c_4251, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_4215, c_607])).
% 13.64/6.31  tff(c_4074, plain, (m1_subset_1('#skF_9', k3_zfmisc_1('#skF_3', '#skF_4', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_4068, c_54])).
% 13.64/6.31  tff(c_4700, plain, (![A_304, B_305, C_306, D_307]: (k7_mcart_1(A_304, B_305, C_306, D_307)=k2_mcart_1(D_307) | ~m1_subset_1(D_307, k3_zfmisc_1(A_304, B_305, C_306)) | k1_xboole_0=C_306 | k1_xboole_0=B_305 | k1_xboole_0=A_304)), inference(cnfTransformation, [status(thm)], [f_107])).
% 13.64/6.31  tff(c_4703, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_8', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_4074, c_4700])).
% 13.64/6.31  tff(c_4706, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_8', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_4250, c_4251, c_4703])).
% 13.64/6.31  tff(c_4707, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_4706])).
% 13.64/6.31  tff(c_294, plain, (![C_81]: (r1_xboole_0(C_81, k1_xboole_0))), inference(resolution, [status(thm)], [c_286, c_6])).
% 13.64/6.31  tff(c_76, plain, (![A_57, B_58]: (k3_xboole_0(A_57, B_58)=A_57 | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_69])).
% 13.64/6.31  tff(c_87, plain, (![B_13]: (k3_xboole_0(B_13, B_13)=B_13)), inference(resolution, [status(thm)], [c_16, c_76])).
% 13.64/6.31  tff(c_234, plain, (![A_75, B_76, C_77]: (~r1_xboole_0(A_75, B_76) | ~r2_hidden(C_77, k3_xboole_0(A_75, B_76)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.64/6.31  tff(c_490, plain, (![B_93, C_94]: (~r1_xboole_0(B_93, B_93) | ~r2_hidden(C_94, B_93))), inference(superposition, [status(thm), theory('equality')], [c_87, c_234])).
% 13.64/6.31  tff(c_503, plain, (![C_94]: (~r2_hidden(C_94, k1_xboole_0))), inference(resolution, [status(thm)], [c_294, c_490])).
% 13.64/6.31  tff(c_4734, plain, (![C_94]: (~r2_hidden(C_94, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_4707, c_503])).
% 13.64/6.31  tff(c_4334, plain, (![A_292, B_293, C_294]: (k2_zfmisc_1(k2_zfmisc_1(A_292, B_293), C_294)=k3_zfmisc_1(A_292, B_293, C_294))), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.64/6.31  tff(c_40, plain, (![A_29, C_31, B_30]: (r2_hidden(k2_mcart_1(A_29), C_31) | ~r2_hidden(A_29, k2_zfmisc_1(B_30, C_31)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.64/6.31  tff(c_6032, plain, (![A_375, C_376, A_377, B_378]: (r2_hidden(k2_mcart_1(A_375), C_376) | ~r2_hidden(A_375, k3_zfmisc_1(A_377, B_378, C_376)))), inference(superposition, [status(thm), theory('equality')], [c_4334, c_40])).
% 13.64/6.31  tff(c_6034, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_52, c_6032])).
% 13.64/6.31  tff(c_6041, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4734, c_6034])).
% 13.64/6.31  tff(c_6043, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_4706])).
% 13.64/6.31  tff(c_6337, plain, (![A_389, B_390, C_391, D_392]: (k5_mcart_1(A_389, B_390, C_391, D_392)=k1_mcart_1(k1_mcart_1(D_392)) | ~m1_subset_1(D_392, k3_zfmisc_1(A_389, B_390, C_391)) | k1_xboole_0=C_391 | k1_xboole_0=B_390 | k1_xboole_0=A_389)), inference(cnfTransformation, [status(thm)], [f_107])).
% 13.64/6.31  tff(c_6340, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_8', '#skF_9') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_4074, c_6337])).
% 13.64/6.31  tff(c_6343, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_4250, c_4251, c_6043, c_6340])).
% 13.64/6.31  tff(c_9943, plain, (![A_525, A_526, B_527, C_528]: (r2_hidden(k1_mcart_1(A_525), k2_zfmisc_1(A_526, B_527)) | ~r2_hidden(A_525, k3_zfmisc_1(A_526, B_527, C_528)))), inference(superposition, [status(thm), theory('equality')], [c_4334, c_42])).
% 13.64/6.31  tff(c_9967, plain, (r2_hidden(k1_mcart_1('#skF_9'), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_52, c_9943])).
% 13.64/6.31  tff(c_9975, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')), '#skF_6')), inference(resolution, [status(thm)], [c_9967, c_42])).
% 13.64/6.31  tff(c_9992, plain, (r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_8', '#skF_9'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6343, c_9975])).
% 13.64/6.31  tff(c_9994, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4071, c_9992])).
% 13.64/6.31  tff(c_9995, plain, ('#skF_6'='#skF_3'), inference(splitRight, [status(thm)], [c_574])).
% 13.64/6.31  tff(c_9999, plain, (~r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9995, c_144])).
% 13.64/6.31  tff(c_10043, plain, (![A_530, B_531, C_532]: (r2_hidden(k1_mcart_1(A_530), B_531) | ~r2_hidden(A_530, k2_zfmisc_1(B_531, C_532)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.64/6.31  tff(c_13459, plain, (![B_696, C_697]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_696, C_697))), B_696) | v1_xboole_0(k2_zfmisc_1(B_696, C_697)))), inference(resolution, [status(thm)], [c_4, c_10043])).
% 13.64/6.31  tff(c_10120, plain, (![A_535, B_536]: (r1_tarski(A_535, B_536) | ~r1_tarski(A_535, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_135, c_412])).
% 13.64/6.31  tff(c_10126, plain, (![A_14, B_536]: (r1_tarski(A_14, B_536) | k4_xboole_0(A_14, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_10120])).
% 13.64/6.31  tff(c_10143, plain, (![A_537, B_538]: (r1_tarski(A_537, B_538) | k1_xboole_0!=A_537)), inference(demodulation, [status(thm), theory('equality')], [c_301, c_10126])).
% 13.64/6.31  tff(c_10175, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_10143, c_607])).
% 13.64/6.31  tff(c_10027, plain, (![A_529]: (r1_tarski(A_529, '#skF_8') | k1_xboole_0!=A_529)), inference(demodulation, [status(thm), theory('equality')], [c_301, c_523])).
% 13.64/6.31  tff(c_10018, plain, (~r1_tarski('#skF_5', '#skF_8')), inference(splitLeft, [status(thm)], [c_575])).
% 13.64/6.31  tff(c_10039, plain, (k1_xboole_0!='#skF_5'), inference(resolution, [status(thm)], [c_10027, c_10018])).
% 13.64/6.31  tff(c_10393, plain, (![A_555, B_556, C_557, D_558]: (k7_mcart_1(A_555, B_556, C_557, D_558)=k2_mcart_1(D_558) | ~m1_subset_1(D_558, k3_zfmisc_1(A_555, B_556, C_557)) | k1_xboole_0=C_557 | k1_xboole_0=B_556 | k1_xboole_0=A_555)), inference(cnfTransformation, [status(thm)], [f_107])).
% 13.64/6.31  tff(c_10396, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_54, c_10393])).
% 13.64/6.31  tff(c_10399, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_10175, c_10039, c_10396])).
% 13.64/6.31  tff(c_10867, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_10399])).
% 13.64/6.31  tff(c_10897, plain, (![C_94]: (~r2_hidden(C_94, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_10867, c_503])).
% 13.64/6.31  tff(c_13504, plain, (![C_698]: (v1_xboole_0(k2_zfmisc_1('#skF_3', C_698)))), inference(resolution, [status(thm)], [c_13459, c_10897])).
% 13.64/6.31  tff(c_10901, plain, (![B_13]: (k4_xboole_0(B_13, B_13)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10867, c_135])).
% 13.64/6.31  tff(c_10302, plain, (![A_551, B_552]: (r2_hidden('#skF_2'(A_551, B_552), k3_xboole_0(A_551, B_552)) | r1_xboole_0(A_551, B_552))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.64/6.31  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.64/6.31  tff(c_11279, plain, (![A_592, B_593]: (~v1_xboole_0(k3_xboole_0(A_592, B_593)) | r1_xboole_0(A_592, B_593))), inference(resolution, [status(thm)], [c_10302, c_2])).
% 13.64/6.31  tff(c_11329, plain, (![B_595]: (~v1_xboole_0(B_595) | r1_xboole_0(B_595, B_595))), inference(superposition, [status(thm), theory('equality')], [c_87, c_11279])).
% 13.64/6.31  tff(c_11337, plain, (![B_595]: (k4_xboole_0(B_595, B_595)=B_595 | ~v1_xboole_0(B_595))), inference(resolution, [status(thm)], [c_11329, c_30])).
% 13.64/6.31  tff(c_11343, plain, (![B_595]: (B_595='#skF_3' | ~v1_xboole_0(B_595))), inference(demodulation, [status(thm), theory('equality')], [c_10901, c_11337])).
% 13.64/6.31  tff(c_13514, plain, (![C_698]: (k2_zfmisc_1('#skF_3', C_698)='#skF_3')), inference(resolution, [status(thm)], [c_13504, c_11343])).
% 13.64/6.31  tff(c_13518, plain, (![C_699]: (k2_zfmisc_1('#skF_3', C_699)='#skF_3')), inference(resolution, [status(thm)], [c_13504, c_11343])).
% 13.64/6.31  tff(c_13540, plain, (![C_699, C_28]: (k3_zfmisc_1('#skF_3', C_699, C_28)=k2_zfmisc_1('#skF_3', C_28))), inference(superposition, [status(thm), theory('equality')], [c_13518, c_38])).
% 13.64/6.31  tff(c_13555, plain, (![C_699, C_28]: (k3_zfmisc_1('#skF_3', C_699, C_28)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_13514, c_13540])).
% 13.64/6.31  tff(c_10003, plain, (r2_hidden('#skF_9', k3_zfmisc_1('#skF_3', '#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_9995, c_52])).
% 13.64/6.31  tff(c_10235, plain, (![A_546, B_547]: (r1_xboole_0(A_546, B_547) | ~r1_tarski(A_546, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_135, c_255])).
% 13.64/6.31  tff(c_249, plain, (![B_13, C_77]: (~r1_xboole_0(B_13, B_13) | ~r2_hidden(C_77, B_13))), inference(superposition, [status(thm), theory('equality')], [c_87, c_234])).
% 13.64/6.31  tff(c_10400, plain, (![C_559, B_560]: (~r2_hidden(C_559, B_560) | ~r1_tarski(B_560, k1_xboole_0))), inference(resolution, [status(thm)], [c_10235, c_249])).
% 13.64/6.31  tff(c_10419, plain, (~r1_tarski(k3_zfmisc_1('#skF_3', '#skF_7', '#skF_8'), k1_xboole_0)), inference(resolution, [status(thm)], [c_10003, c_10400])).
% 13.64/6.31  tff(c_10873, plain, (~r1_tarski(k3_zfmisc_1('#skF_3', '#skF_7', '#skF_8'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10867, c_10419])).
% 13.64/6.31  tff(c_13559, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_13555, c_10873])).
% 13.64/6.31  tff(c_13567, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_13559])).
% 13.64/6.31  tff(c_13569, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_10399])).
% 13.64/6.31  tff(c_13630, plain, (![A_702, B_703, C_704, D_705]: (k5_mcart_1(A_702, B_703, C_704, D_705)=k1_mcart_1(k1_mcart_1(D_705)) | ~m1_subset_1(D_705, k3_zfmisc_1(A_702, B_703, C_704)) | k1_xboole_0=C_704 | k1_xboole_0=B_703 | k1_xboole_0=A_702)), inference(cnfTransformation, [status(thm)], [f_107])).
% 13.64/6.31  tff(c_13633, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_54, c_13630])).
% 13.64/6.31  tff(c_13636, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_13569, c_10175, c_10039, c_13633])).
% 13.64/6.31  tff(c_10182, plain, (![A_539, B_540, C_541]: (k2_zfmisc_1(k2_zfmisc_1(A_539, B_540), C_541)=k3_zfmisc_1(A_539, B_540, C_541))), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.64/6.31  tff(c_16727, plain, (![A_854, A_855, B_856, C_857]: (r2_hidden(k1_mcart_1(A_854), k2_zfmisc_1(A_855, B_856)) | ~r2_hidden(A_854, k3_zfmisc_1(A_855, B_856, C_857)))), inference(superposition, [status(thm), theory('equality')], [c_10182, c_42])).
% 13.64/6.31  tff(c_16754, plain, (r2_hidden(k1_mcart_1('#skF_9'), k2_zfmisc_1('#skF_3', '#skF_7'))), inference(resolution, [status(thm)], [c_10003, c_16727])).
% 13.64/6.31  tff(c_16762, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')), '#skF_3')), inference(resolution, [status(thm)], [c_16754, c_42])).
% 13.64/6.31  tff(c_16779, plain, (r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_13636, c_16762])).
% 13.64/6.31  tff(c_16781, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9999, c_16779])).
% 13.64/6.31  tff(c_16782, plain, ('#skF_5'='#skF_8'), inference(splitRight, [status(thm)], [c_575])).
% 13.64/6.31  tff(c_17017, plain, (~r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_8', '#skF_9'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16782, c_9999])).
% 13.64/6.31  tff(c_17010, plain, (![A_874, B_875, C_876]: (r2_hidden(k1_mcart_1(A_874), B_875) | ~r2_hidden(A_874, k2_zfmisc_1(B_875, C_876)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.64/6.31  tff(c_18847, plain, (![B_981, C_982]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_981, C_982))), B_981) | v1_xboole_0(k2_zfmisc_1(B_981, C_982)))), inference(resolution, [status(thm)], [c_4, c_17010])).
% 13.64/6.31  tff(c_16845, plain, (![A_864, B_865]: (r1_tarski(A_864, B_865) | ~r1_tarski(A_864, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_135, c_412])).
% 13.64/6.31  tff(c_16851, plain, (![A_14, B_865]: (r1_tarski(A_14, B_865) | k4_xboole_0(A_14, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_16845])).
% 13.64/6.31  tff(c_16876, plain, (![A_866, B_867]: (r1_tarski(A_866, B_867) | k1_xboole_0!=A_866)), inference(demodulation, [status(thm), theory('equality')], [c_301, c_16851])).
% 13.64/6.31  tff(c_16908, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_16876, c_607])).
% 13.64/6.31  tff(c_16787, plain, (m1_subset_1('#skF_9', k3_zfmisc_1('#skF_3', '#skF_4', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_16782, c_54])).
% 13.64/6.31  tff(c_17536, plain, (![A_898, B_899, C_900, D_901]: (k7_mcart_1(A_898, B_899, C_900, D_901)=k2_mcart_1(D_901) | ~m1_subset_1(D_901, k3_zfmisc_1(A_898, B_899, C_900)) | k1_xboole_0=C_900 | k1_xboole_0=B_899 | k1_xboole_0=A_898)), inference(cnfTransformation, [status(thm)], [f_107])).
% 13.64/6.31  tff(c_17539, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_8', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_16787, c_17536])).
% 13.64/6.31  tff(c_17542, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_8', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_16908, c_17539])).
% 13.64/6.31  tff(c_17606, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_17542])).
% 13.64/6.31  tff(c_17630, plain, (![C_94]: (~r2_hidden(C_94, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_17606, c_503])).
% 13.64/6.31  tff(c_18892, plain, (![C_983]: (v1_xboole_0(k2_zfmisc_1('#skF_3', C_983)))), inference(resolution, [status(thm)], [c_18847, c_17630])).
% 13.64/6.31  tff(c_17633, plain, (![B_13]: (k4_xboole_0(B_13, B_13)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_17606, c_135])).
% 13.64/6.31  tff(c_17230, plain, (![A_890, B_891]: (r2_hidden('#skF_2'(A_890, B_891), k3_xboole_0(A_890, B_891)) | r1_xboole_0(A_890, B_891))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.64/6.31  tff(c_17587, plain, (![A_905, B_906]: (~v1_xboole_0(k3_xboole_0(A_905, B_906)) | r1_xboole_0(A_905, B_906))), inference(resolution, [status(thm)], [c_17230, c_2])).
% 13.64/6.31  tff(c_17975, plain, (![B_926]: (~v1_xboole_0(B_926) | r1_xboole_0(B_926, B_926))), inference(superposition, [status(thm), theory('equality')], [c_87, c_17587])).
% 13.64/6.31  tff(c_17983, plain, (![B_926]: (k4_xboole_0(B_926, B_926)=B_926 | ~v1_xboole_0(B_926))), inference(resolution, [status(thm)], [c_17975, c_30])).
% 13.64/6.31  tff(c_17989, plain, (![B_926]: (B_926='#skF_3' | ~v1_xboole_0(B_926))), inference(demodulation, [status(thm), theory('equality')], [c_17633, c_17983])).
% 13.64/6.31  tff(c_18899, plain, (![C_983]: (k2_zfmisc_1('#skF_3', C_983)='#skF_3')), inference(resolution, [status(thm)], [c_18892, c_17989])).
% 13.64/6.31  tff(c_18903, plain, (![C_984]: (k2_zfmisc_1('#skF_3', C_984)='#skF_3')), inference(resolution, [status(thm)], [c_18892, c_17989])).
% 13.64/6.31  tff(c_18923, plain, (![C_984, C_28]: (k3_zfmisc_1('#skF_3', C_984, C_28)=k2_zfmisc_1('#skF_3', C_28))), inference(superposition, [status(thm), theory('equality')], [c_18903, c_38])).
% 13.64/6.31  tff(c_18940, plain, (![C_984, C_28]: (k3_zfmisc_1('#skF_3', C_984, C_28)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18899, c_18923])).
% 13.64/6.31  tff(c_16824, plain, (![A_862, B_863]: (r1_xboole_0(A_862, B_863) | ~r1_tarski(A_862, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_135, c_255])).
% 13.64/6.31  tff(c_17168, plain, (![C_885, B_886]: (~r2_hidden(C_885, B_886) | ~r1_tarski(B_886, k1_xboole_0))), inference(resolution, [status(thm)], [c_16824, c_249])).
% 13.64/6.31  tff(c_17175, plain, (~r1_tarski(k3_zfmisc_1('#skF_3', '#skF_7', '#skF_8'), k1_xboole_0)), inference(resolution, [status(thm)], [c_10003, c_17168])).
% 13.64/6.31  tff(c_17610, plain, (~r1_tarski(k3_zfmisc_1('#skF_3', '#skF_7', '#skF_8'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_17606, c_17175])).
% 13.64/6.31  tff(c_18944, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18940, c_17610])).
% 13.64/6.31  tff(c_18952, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_18944])).
% 13.64/6.31  tff(c_18954, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_17542])).
% 13.64/6.31  tff(c_19161, plain, (![A_995, B_996, C_997, D_998]: (k5_mcart_1(A_995, B_996, C_997, D_998)=k1_mcart_1(k1_mcart_1(D_998)) | ~m1_subset_1(D_998, k3_zfmisc_1(A_995, B_996, C_997)) | k1_xboole_0=C_997 | k1_xboole_0=B_996 | k1_xboole_0=A_995)), inference(cnfTransformation, [status(thm)], [f_107])).
% 13.64/6.31  tff(c_19164, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_8', '#skF_9') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_16787, c_19161])).
% 13.64/6.31  tff(c_19167, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_8', '#skF_9') | k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_18954, c_16908, c_19164])).
% 13.64/6.31  tff(c_19262, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_19167])).
% 13.64/6.31  tff(c_19292, plain, (![C_94]: (~r2_hidden(C_94, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_19262, c_503])).
% 13.64/6.31  tff(c_17088, plain, (![A_879, B_880, C_881]: (k2_zfmisc_1(k2_zfmisc_1(A_879, B_880), C_881)=k3_zfmisc_1(A_879, B_880, C_881))), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.64/6.31  tff(c_20021, plain, (![A_1037, C_1038, A_1039, B_1040]: (r2_hidden(k2_mcart_1(A_1037), C_1038) | ~r2_hidden(A_1037, k3_zfmisc_1(A_1039, B_1040, C_1038)))), inference(superposition, [status(thm), theory('equality')], [c_17088, c_40])).
% 13.64/6.31  tff(c_20023, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_10003, c_20021])).
% 13.64/6.31  tff(c_20030, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19292, c_20023])).
% 13.64/6.31  tff(c_20031, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_19167])).
% 13.64/6.31  tff(c_24694, plain, (![A_1212, A_1213, B_1214, C_1215]: (r2_hidden(k1_mcart_1(A_1212), k2_zfmisc_1(A_1213, B_1214)) | ~r2_hidden(A_1212, k3_zfmisc_1(A_1213, B_1214, C_1215)))), inference(superposition, [status(thm), theory('equality')], [c_17088, c_42])).
% 13.64/6.31  tff(c_24721, plain, (r2_hidden(k1_mcart_1('#skF_9'), k2_zfmisc_1('#skF_3', '#skF_7'))), inference(resolution, [status(thm)], [c_10003, c_24694])).
% 13.64/6.31  tff(c_24727, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')), '#skF_3')), inference(resolution, [status(thm)], [c_24721, c_42])).
% 13.64/6.31  tff(c_24744, plain, (r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_8', '#skF_9'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20031, c_24727])).
% 13.64/6.31  tff(c_24746, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17017, c_24744])).
% 13.64/6.31  tff(c_24747, plain, ('#skF_7'='#skF_4'), inference(splitRight, [status(thm)], [c_573])).
% 13.64/6.31  tff(c_116, plain, (![A_63, B_64]: (r1_xboole_0(A_63, B_64) | k4_xboole_0(A_63, B_64)!=A_63)), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.64/6.31  tff(c_123, plain, (![B_64, A_63]: (r1_xboole_0(B_64, A_63) | k4_xboole_0(A_63, B_64)!=A_63)), inference(resolution, [status(thm)], [c_116, c_6])).
% 13.64/6.31  tff(c_196, plain, (k3_xboole_0('#skF_7', '#skF_4')='#skF_7'), inference(resolution, [status(thm)], [c_172, c_26])).
% 13.64/6.31  tff(c_237, plain, (![C_77]: (~r1_xboole_0('#skF_7', '#skF_4') | ~r2_hidden(C_77, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_196, c_234])).
% 13.64/6.31  tff(c_337, plain, (~r1_xboole_0('#skF_7', '#skF_4')), inference(splitLeft, [status(thm)], [c_237])).
% 13.64/6.31  tff(c_344, plain, (k4_xboole_0('#skF_4', '#skF_7')!='#skF_4'), inference(resolution, [status(thm)], [c_123, c_337])).
% 13.64/6.31  tff(c_24749, plain, (k4_xboole_0('#skF_4', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24747, c_344])).
% 13.64/6.31  tff(c_24758, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_135, c_24749])).
% 13.64/6.31  tff(c_24802, plain, (![A_1219]: (r1_tarski(A_1219, '#skF_8') | k1_xboole_0!=A_1219)), inference(demodulation, [status(thm), theory('equality')], [c_301, c_523])).
% 13.64/6.31  tff(c_24792, plain, (~r1_tarski('#skF_5', '#skF_8')), inference(splitLeft, [status(thm)], [c_575])).
% 13.64/6.31  tff(c_24814, plain, (k1_xboole_0!='#skF_5'), inference(resolution, [status(thm)], [c_24802, c_24792])).
% 13.64/6.31  tff(c_25274, plain, (![A_1249, B_1250, C_1251, D_1252]: (k5_mcart_1(A_1249, B_1250, C_1251, D_1252)=k1_mcart_1(k1_mcart_1(D_1252)) | ~m1_subset_1(D_1252, k3_zfmisc_1(A_1249, B_1250, C_1251)) | k1_xboole_0=C_1251 | k1_xboole_0=B_1250 | k1_xboole_0=A_1249)), inference(cnfTransformation, [status(thm)], [f_107])).
% 13.64/6.31  tff(c_25277, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_54, c_25274])).
% 13.64/6.31  tff(c_25280, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_24989, c_24758, c_24814, c_25277])).
% 13.64/6.31  tff(c_24756, plain, (r2_hidden('#skF_9', k3_zfmisc_1('#skF_6', '#skF_4', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_24747, c_52])).
% 13.64/6.31  tff(c_24996, plain, (![A_1231, B_1232, C_1233]: (r2_hidden(k1_mcart_1(A_1231), B_1232) | ~r2_hidden(A_1231, k2_zfmisc_1(B_1232, C_1233)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.64/6.31  tff(c_28147, plain, (![A_1399, A_1400, B_1401, C_1402]: (r2_hidden(k1_mcart_1(A_1399), k2_zfmisc_1(A_1400, B_1401)) | ~r2_hidden(A_1399, k3_zfmisc_1(A_1400, B_1401, C_1402)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_24996])).
% 13.64/6.31  tff(c_28174, plain, (r2_hidden(k1_mcart_1('#skF_9'), k2_zfmisc_1('#skF_6', '#skF_4'))), inference(resolution, [status(thm)], [c_24756, c_28147])).
% 13.64/6.31  tff(c_28180, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')), '#skF_6')), inference(resolution, [status(thm)], [c_28174, c_42])).
% 13.64/6.31  tff(c_28197, plain, (r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_25280, c_28180])).
% 13.64/6.31  tff(c_28199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_144, c_28197])).
% 13.64/6.31  tff(c_28200, plain, ('#skF_5'='#skF_8'), inference(splitRight, [status(thm)], [c_575])).
% 13.64/6.31  tff(c_28203, plain, (~r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_8', '#skF_9'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_28200, c_144])).
% 13.64/6.31  tff(c_28344, plain, (![A_1411, B_1412]: (r1_tarski(A_1411, B_1412) | ~r1_tarski(A_1411, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_135, c_412])).
% 13.64/6.31  tff(c_28350, plain, (![A_14, B_1412]: (r1_tarski(A_14, B_1412) | k4_xboole_0(A_14, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_28344])).
% 13.64/6.31  tff(c_28367, plain, (![A_1413, B_1414]: (r1_tarski(A_1413, B_1414) | k1_xboole_0!=A_1413)), inference(demodulation, [status(thm), theory('equality')], [c_301, c_28350])).
% 13.64/6.31  tff(c_28399, plain, (k1_xboole_0!='#skF_3'), inference(resolution, [status(thm)], [c_28367, c_24782])).
% 13.64/6.31  tff(c_28206, plain, (m1_subset_1('#skF_9', k3_zfmisc_1('#skF_3', '#skF_4', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_28200, c_54])).
% 13.64/6.31  tff(c_28604, plain, (![A_1428, B_1429, C_1430, D_1431]: (k7_mcart_1(A_1428, B_1429, C_1430, D_1431)=k2_mcart_1(D_1431) | ~m1_subset_1(D_1431, k3_zfmisc_1(A_1428, B_1429, C_1430)) | k1_xboole_0=C_1430 | k1_xboole_0=B_1429 | k1_xboole_0=A_1428)), inference(cnfTransformation, [status(thm)], [f_107])).
% 13.64/6.31  tff(c_28607, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_8', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_28206, c_28604])).
% 13.64/6.31  tff(c_28610, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_8', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_28399, c_24758, c_28607])).
% 13.64/6.31  tff(c_29166, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_28610])).
% 13.64/6.31  tff(c_29196, plain, (![C_94]: (~r2_hidden(C_94, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_29166, c_503])).
% 13.64/6.31  tff(c_28239, plain, (![A_1404, B_1405, C_1406]: (k2_zfmisc_1(k2_zfmisc_1(A_1404, B_1405), C_1406)=k3_zfmisc_1(A_1404, B_1405, C_1406))), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.64/6.31  tff(c_29804, plain, (![A_1486, C_1487, A_1488, B_1489]: (r2_hidden(k2_mcart_1(A_1486), C_1487) | ~r2_hidden(A_1486, k3_zfmisc_1(A_1488, B_1489, C_1487)))), inference(superposition, [status(thm), theory('equality')], [c_28239, c_40])).
% 13.64/6.31  tff(c_29806, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_24756, c_29804])).
% 13.64/6.31  tff(c_29813, plain, $false, inference(negUnitSimplification, [status(thm)], [c_29196, c_29806])).
% 13.64/6.31  tff(c_29815, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_28610])).
% 13.64/6.31  tff(c_28858, plain, (![A_1441, B_1442, C_1443, D_1444]: (k5_mcart_1(A_1441, B_1442, C_1443, D_1444)=k1_mcart_1(k1_mcart_1(D_1444)) | ~m1_subset_1(D_1444, k3_zfmisc_1(A_1441, B_1442, C_1443)) | k1_xboole_0=C_1443 | k1_xboole_0=B_1442 | k1_xboole_0=A_1441)), inference(cnfTransformation, [status(thm)], [f_107])).
% 13.64/6.31  tff(c_28861, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_8', '#skF_9') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_28206, c_28858])).
% 13.64/6.31  tff(c_28864, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_8', '#skF_9') | k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_28399, c_24758, c_28861])).
% 13.64/6.31  tff(c_29902, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_29815, c_28864])).
% 13.64/6.31  tff(c_28424, plain, (![A_1417, B_1418, C_1419]: (r2_hidden(k1_mcart_1(A_1417), B_1418) | ~r2_hidden(A_1417, k2_zfmisc_1(B_1418, C_1419)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.64/6.31  tff(c_32970, plain, (![A_1640, A_1641, B_1642, C_1643]: (r2_hidden(k1_mcart_1(A_1640), k2_zfmisc_1(A_1641, B_1642)) | ~r2_hidden(A_1640, k3_zfmisc_1(A_1641, B_1642, C_1643)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_28424])).
% 13.64/6.31  tff(c_32997, plain, (r2_hidden(k1_mcart_1('#skF_9'), k2_zfmisc_1('#skF_6', '#skF_4'))), inference(resolution, [status(thm)], [c_24756, c_32970])).
% 13.64/6.31  tff(c_33003, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')), '#skF_6')), inference(resolution, [status(thm)], [c_32997, c_42])).
% 13.64/6.31  tff(c_33020, plain, (r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_8', '#skF_9'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_29902, c_33003])).
% 13.64/6.31  tff(c_33022, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28203, c_33020])).
% 13.64/6.31  tff(c_33023, plain, ('#skF_6'='#skF_3'), inference(splitRight, [status(thm)], [c_574])).
% 13.64/6.31  tff(c_33026, plain, (~r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_33023, c_144])).
% 13.64/6.31  tff(c_33069, plain, (![A_1645, B_1646, C_1647]: (r2_hidden(k1_mcart_1(A_1645), B_1646) | ~r2_hidden(A_1645, k2_zfmisc_1(B_1646, C_1647)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.64/6.31  tff(c_36287, plain, (![B_1825, C_1826]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_1825, C_1826))), B_1825) | v1_xboole_0(k2_zfmisc_1(B_1825, C_1826)))), inference(resolution, [status(thm)], [c_4, c_33069])).
% 13.64/6.31  tff(c_33053, plain, (![A_1644]: (r1_tarski(A_1644, '#skF_8') | k1_xboole_0!=A_1644)), inference(demodulation, [status(thm), theory('equality')], [c_301, c_523])).
% 13.64/6.31  tff(c_33043, plain, (~r1_tarski('#skF_5', '#skF_8')), inference(splitLeft, [status(thm)], [c_575])).
% 13.64/6.31  tff(c_33065, plain, (k1_xboole_0!='#skF_5'), inference(resolution, [status(thm)], [c_33053, c_33043])).
% 13.64/6.31  tff(c_33529, plain, (![A_1677, B_1678, C_1679, D_1680]: (k7_mcart_1(A_1677, B_1678, C_1679, D_1680)=k2_mcart_1(D_1680) | ~m1_subset_1(D_1680, k3_zfmisc_1(A_1677, B_1678, C_1679)) | k1_xboole_0=C_1679 | k1_xboole_0=B_1678 | k1_xboole_0=A_1677)), inference(cnfTransformation, [status(thm)], [f_107])).
% 13.64/6.31  tff(c_33532, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_54, c_33529])).
% 13.64/6.31  tff(c_33535, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_24758, c_33065, c_33532])).
% 13.64/6.31  tff(c_33627, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_33535])).
% 13.64/6.31  tff(c_33652, plain, (![C_94]: (~r2_hidden(C_94, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_33627, c_503])).
% 13.64/6.31  tff(c_36337, plain, (![C_1827]: (v1_xboole_0(k2_zfmisc_1('#skF_3', C_1827)))), inference(resolution, [status(thm)], [c_36287, c_33652])).
% 13.64/6.31  tff(c_33655, plain, (![B_13]: (k4_xboole_0(B_13, B_13)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_33627, c_135])).
% 13.64/6.31  tff(c_33354, plain, (![A_1669, B_1670]: (r2_hidden('#skF_2'(A_1669, B_1670), k3_xboole_0(A_1669, B_1670)) | r1_xboole_0(A_1669, B_1670))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.64/6.31  tff(c_34134, plain, (![A_1712, B_1713]: (~v1_xboole_0(k3_xboole_0(A_1712, B_1713)) | r1_xboole_0(A_1712, B_1713))), inference(resolution, [status(thm)], [c_33354, c_2])).
% 13.64/6.31  tff(c_34155, plain, (![B_1714]: (~v1_xboole_0(B_1714) | r1_xboole_0(B_1714, B_1714))), inference(superposition, [status(thm), theory('equality')], [c_87, c_34134])).
% 13.64/6.31  tff(c_34166, plain, (![B_1714]: (k4_xboole_0(B_1714, B_1714)=B_1714 | ~v1_xboole_0(B_1714))), inference(resolution, [status(thm)], [c_34155, c_30])).
% 13.64/6.31  tff(c_34173, plain, (![B_1714]: (B_1714='#skF_3' | ~v1_xboole_0(B_1714))), inference(demodulation, [status(thm), theory('equality')], [c_33655, c_34166])).
% 13.64/6.31  tff(c_36347, plain, (![C_1827]: (k2_zfmisc_1('#skF_3', C_1827)='#skF_3')), inference(resolution, [status(thm)], [c_36337, c_34173])).
% 13.64/6.31  tff(c_36351, plain, (![C_1828]: (k2_zfmisc_1('#skF_3', C_1828)='#skF_3')), inference(resolution, [status(thm)], [c_36337, c_34173])).
% 13.64/6.31  tff(c_36371, plain, (![C_1828, C_28]: (k3_zfmisc_1('#skF_3', C_1828, C_28)=k2_zfmisc_1('#skF_3', C_28))), inference(superposition, [status(thm), theory('equality')], [c_36351, c_38])).
% 13.64/6.31  tff(c_36388, plain, (![C_1828, C_28]: (k3_zfmisc_1('#skF_3', C_1828, C_28)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36347, c_36371])).
% 13.64/6.31  tff(c_33076, plain, (r2_hidden('#skF_9', k3_zfmisc_1('#skF_3', '#skF_4', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_33023, c_24756])).
% 13.64/6.31  tff(c_33245, plain, (![A_1661, A_1662]: (r1_xboole_0(A_1661, A_1662) | ~r1_tarski(A_1661, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_136, c_255])).
% 13.64/6.31  tff(c_33321, plain, (![C_1666, A_1667]: (~r2_hidden(C_1666, A_1667) | ~r1_tarski(A_1667, k1_xboole_0))), inference(resolution, [status(thm)], [c_33245, c_249])).
% 13.64/6.31  tff(c_33328, plain, (~r1_tarski(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_8'), k1_xboole_0)), inference(resolution, [status(thm)], [c_33076, c_33321])).
% 13.64/6.31  tff(c_33628, plain, (~r1_tarski(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_8'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_33627, c_33328])).
% 13.64/6.31  tff(c_36392, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36388, c_33628])).
% 13.64/6.31  tff(c_36400, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_36392])).
% 13.64/6.31  tff(c_36402, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_33535])).
% 13.64/6.31  tff(c_36842, plain, (![A_1850, B_1851, C_1852, D_1853]: (k5_mcart_1(A_1850, B_1851, C_1852, D_1853)=k1_mcart_1(k1_mcart_1(D_1853)) | ~m1_subset_1(D_1853, k3_zfmisc_1(A_1850, B_1851, C_1852)) | k1_xboole_0=C_1852 | k1_xboole_0=B_1851 | k1_xboole_0=A_1850)), inference(cnfTransformation, [status(thm)], [f_107])).
% 13.64/6.31  tff(c_36845, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_54, c_36842])).
% 13.64/6.31  tff(c_36848, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_36402, c_24758, c_33065, c_36845])).
% 13.64/6.31  tff(c_33293, plain, (![A_1663, B_1664, C_1665]: (k2_zfmisc_1(k2_zfmisc_1(A_1663, B_1664), C_1665)=k3_zfmisc_1(A_1663, B_1664, C_1665))), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.64/6.31  tff(c_39788, plain, (![A_1972, A_1973, B_1974, C_1975]: (r2_hidden(k1_mcart_1(A_1972), k2_zfmisc_1(A_1973, B_1974)) | ~r2_hidden(A_1972, k3_zfmisc_1(A_1973, B_1974, C_1975)))), inference(superposition, [status(thm), theory('equality')], [c_33293, c_42])).
% 13.64/6.31  tff(c_39812, plain, (r2_hidden(k1_mcart_1('#skF_9'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_33076, c_39788])).
% 13.64/6.31  tff(c_39820, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')), '#skF_3')), inference(resolution, [status(thm)], [c_39812, c_42])).
% 13.64/6.31  tff(c_39834, plain, (r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36848, c_39820])).
% 13.64/6.31  tff(c_39836, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33026, c_39834])).
% 13.64/6.31  tff(c_39837, plain, ('#skF_5'='#skF_8'), inference(splitRight, [status(thm)], [c_575])).
% 13.64/6.31  tff(c_40142, plain, (~r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_8', '#skF_9'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_39837, c_33026])).
% 13.64/6.31  tff(c_40146, plain, (![A_1997, B_1998, C_1999]: (r2_hidden(k1_mcart_1(A_1997), B_1998) | ~r2_hidden(A_1997, k2_zfmisc_1(B_1998, C_1999)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.64/6.31  tff(c_42276, plain, (![B_2131, C_2132]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_2131, C_2132))), B_2131) | v1_xboole_0(k2_zfmisc_1(B_2131, C_2132)))), inference(resolution, [status(thm)], [c_4, c_40146])).
% 13.64/6.31  tff(c_39881, plain, (![A_1980, B_1981]: (r1_tarski(A_1980, B_1981) | ~r1_tarski(A_1980, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_135, c_412])).
% 13.64/6.31  tff(c_39887, plain, (![A_14, B_1981]: (r1_tarski(A_14, B_1981) | k4_xboole_0(A_14, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_39881])).
% 13.64/6.31  tff(c_39897, plain, (![A_14, B_1981]: (r1_tarski(A_14, B_1981) | k1_xboole_0!=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_301, c_39887])).
% 13.64/6.31  tff(c_39863, plain, (![A_1976]: (r1_tarski(A_1976, '#skF_8') | k1_xboole_0!=A_1976)), inference(demodulation, [status(thm), theory('equality')], [c_301, c_523])).
% 13.64/6.31  tff(c_12, plain, (![B_13, A_12]: (B_13=A_12 | ~r1_tarski(B_13, A_12) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.64/6.31  tff(c_40471, plain, (![A_2015]: (A_2015='#skF_8' | ~r1_tarski('#skF_8', A_2015) | k1_xboole_0!=A_2015)), inference(resolution, [status(thm)], [c_39863, c_12])).
% 13.64/6.31  tff(c_40484, plain, (![B_1981]: (B_1981='#skF_8' | k1_xboole_0!=B_1981 | k1_xboole_0!='#skF_8')), inference(resolution, [status(thm)], [c_39897, c_40471])).
% 13.64/6.31  tff(c_40488, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_40484])).
% 13.64/6.31  tff(c_39842, plain, (m1_subset_1('#skF_9', k3_zfmisc_1('#skF_3', '#skF_4', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_39837, c_54])).
% 13.64/6.31  tff(c_40516, plain, (![A_2019, B_2020, C_2021, D_2022]: (k7_mcart_1(A_2019, B_2020, C_2021, D_2022)=k2_mcart_1(D_2022) | ~m1_subset_1(D_2022, k3_zfmisc_1(A_2019, B_2020, C_2021)) | k1_xboole_0=C_2021 | k1_xboole_0=B_2020 | k1_xboole_0=A_2019)), inference(cnfTransformation, [status(thm)], [f_107])).
% 13.64/6.31  tff(c_40519, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_8', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_39842, c_40516])).
% 13.64/6.31  tff(c_40522, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_8', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_24758, c_40488, c_40519])).
% 13.64/6.31  tff(c_40547, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_40522])).
% 13.64/6.31  tff(c_40572, plain, (![C_94]: (~r2_hidden(C_94, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40547, c_503])).
% 13.64/6.31  tff(c_42321, plain, (![C_2133]: (v1_xboole_0(k2_zfmisc_1('#skF_3', C_2133)))), inference(resolution, [status(thm)], [c_42276, c_40572])).
% 13.64/6.31  tff(c_40305, plain, (![A_2009, B_2010]: (r2_hidden('#skF_2'(A_2009, B_2010), k3_xboole_0(A_2009, B_2010)) | r1_xboole_0(A_2009, B_2010))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.64/6.31  tff(c_40489, plain, (![A_2016, B_2017]: (~v1_xboole_0(k3_xboole_0(A_2016, B_2017)) | r1_xboole_0(A_2016, B_2017))), inference(resolution, [status(thm)], [c_40305, c_2])).
% 13.64/6.31  tff(c_40500, plain, (![B_2018]: (~v1_xboole_0(B_2018) | r1_xboole_0(B_2018, B_2018))), inference(superposition, [status(thm), theory('equality')], [c_87, c_40489])).
% 13.64/6.31  tff(c_40508, plain, (![B_2018]: (k4_xboole_0(B_2018, B_2018)=B_2018 | ~v1_xboole_0(B_2018))), inference(resolution, [status(thm)], [c_40500, c_30])).
% 13.64/6.31  tff(c_40514, plain, (![B_2018]: (k1_xboole_0=B_2018 | ~v1_xboole_0(B_2018))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_40508])).
% 13.64/6.31  tff(c_40548, plain, (![B_2018]: (B_2018='#skF_3' | ~v1_xboole_0(B_2018))), inference(demodulation, [status(thm), theory('equality')], [c_40547, c_40514])).
% 13.64/6.31  tff(c_42331, plain, (![C_2133]: (k2_zfmisc_1('#skF_3', C_2133)='#skF_3')), inference(resolution, [status(thm)], [c_42321, c_40548])).
% 13.64/6.31  tff(c_42335, plain, (![C_2134]: (k2_zfmisc_1('#skF_3', C_2134)='#skF_3')), inference(resolution, [status(thm)], [c_42321, c_40548])).
% 13.64/6.31  tff(c_42357, plain, (![C_2134, C_28]: (k3_zfmisc_1('#skF_3', C_2134, C_28)=k2_zfmisc_1('#skF_3', C_28))), inference(superposition, [status(thm), theory('equality')], [c_42335, c_38])).
% 13.64/6.31  tff(c_42373, plain, (![C_2134, C_28]: (k3_zfmisc_1('#skF_3', C_2134, C_28)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42331, c_42357])).
% 13.64/6.31  tff(c_39953, plain, (r2_hidden('#skF_9', k3_zfmisc_1('#skF_3', '#skF_4', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_33023, c_24756])).
% 13.64/6.31  tff(c_39980, plain, (![A_1988, A_1989]: (r1_xboole_0(A_1988, A_1989) | ~r1_tarski(A_1988, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_136, c_255])).
% 13.64/6.31  tff(c_40154, plain, (![C_2000, A_2001]: (~r2_hidden(C_2000, A_2001) | ~r1_tarski(A_2001, k1_xboole_0))), inference(resolution, [status(thm)], [c_39980, c_249])).
% 13.64/6.31  tff(c_40161, plain, (~r1_tarski(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_8'), k1_xboole_0)), inference(resolution, [status(thm)], [c_39953, c_40154])).
% 13.64/6.31  tff(c_40554, plain, (~r1_tarski(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_8'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40547, c_40161])).
% 13.64/6.31  tff(c_42376, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42373, c_40554])).
% 13.64/6.31  tff(c_42384, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_42376])).
% 13.64/6.31  tff(c_42386, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_40522])).
% 13.64/6.31  tff(c_42655, plain, (![A_2147, B_2148, C_2149, D_2150]: (k5_mcart_1(A_2147, B_2148, C_2149, D_2150)=k1_mcart_1(k1_mcart_1(D_2150)) | ~m1_subset_1(D_2150, k3_zfmisc_1(A_2147, B_2148, C_2149)) | k1_xboole_0=C_2149 | k1_xboole_0=B_2148 | k1_xboole_0=A_2147)), inference(cnfTransformation, [status(thm)], [f_107])).
% 13.64/6.31  tff(c_42658, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_8', '#skF_9') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_39842, c_42655])).
% 13.64/6.31  tff(c_42661, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_42386, c_24758, c_40488, c_42658])).
% 13.64/6.31  tff(c_46751, plain, (![A_2293, A_2294, B_2295, C_2296]: (r2_hidden(k1_mcart_1(A_2293), k2_zfmisc_1(A_2294, B_2295)) | ~r2_hidden(A_2293, k3_zfmisc_1(A_2294, B_2295, C_2296)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_40146])).
% 13.64/6.31  tff(c_46775, plain, (r2_hidden(k1_mcart_1('#skF_9'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_39953, c_46751])).
% 13.64/6.31  tff(c_46781, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')), '#skF_3')), inference(resolution, [status(thm)], [c_46775, c_42])).
% 13.64/6.31  tff(c_46795, plain, (r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_8', '#skF_9'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42661, c_46781])).
% 13.64/6.31  tff(c_46797, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40142, c_46795])).
% 13.64/6.31  tff(c_46799, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_40484])).
% 13.64/6.31  tff(c_46821, plain, (![C_94]: (~r2_hidden(C_94, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_46799, c_503])).
% 13.64/6.31  tff(c_40007, plain, (![A_1990, B_1991, C_1992]: (k2_zfmisc_1(k2_zfmisc_1(A_1990, B_1991), C_1992)=k3_zfmisc_1(A_1990, B_1991, C_1992))), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.64/6.31  tff(c_48756, plain, (![A_2414, C_2415, A_2416, B_2417]: (r2_hidden(k2_mcart_1(A_2414), C_2415) | ~r2_hidden(A_2414, k3_zfmisc_1(A_2416, B_2417, C_2415)))), inference(superposition, [status(thm), theory('equality')], [c_40007, c_40])).
% 13.64/6.31  tff(c_48758, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_39953, c_48756])).
% 13.64/6.31  tff(c_48765, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46821, c_48758])).
% 13.64/6.31  tff(c_48766, plain, (![C_77]: (~r2_hidden(C_77, '#skF_7'))), inference(splitRight, [status(thm)], [c_237])).
% 13.64/6.31  tff(c_52479, plain, (![C_2596]: (v1_xboole_0(k2_zfmisc_1('#skF_7', C_2596)))), inference(resolution, [status(thm)], [c_52434, c_48766])).
% 13.64/6.31  tff(c_48767, plain, (r1_xboole_0('#skF_7', '#skF_4')), inference(splitRight, [status(thm)], [c_237])).
% 13.64/6.31  tff(c_48779, plain, (k4_xboole_0('#skF_7', '#skF_4')='#skF_7'), inference(resolution, [status(thm)], [c_48767, c_30])).
% 13.64/6.31  tff(c_195, plain, (k4_xboole_0('#skF_7', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_172, c_20])).
% 13.64/6.31  tff(c_48797, plain, (k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_48779, c_195])).
% 13.64/6.31  tff(c_48812, plain, (![B_13]: (k4_xboole_0(B_13, B_13)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_48797, c_135])).
% 13.64/6.31  tff(c_49305, plain, (![A_2458, B_2459]: (r2_hidden('#skF_2'(A_2458, B_2459), k3_xboole_0(A_2458, B_2459)) | r1_xboole_0(A_2458, B_2459))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.64/6.31  tff(c_49573, plain, (![A_2480, B_2481]: (~v1_xboole_0(k3_xboole_0(A_2480, B_2481)) | r1_xboole_0(A_2480, B_2481))), inference(resolution, [status(thm)], [c_49305, c_2])).
% 13.64/6.31  tff(c_49598, plain, (![B_2482]: (~v1_xboole_0(B_2482) | r1_xboole_0(B_2482, B_2482))), inference(superposition, [status(thm), theory('equality')], [c_87, c_49573])).
% 13.64/6.31  tff(c_49606, plain, (![B_2482]: (k4_xboole_0(B_2482, B_2482)=B_2482 | ~v1_xboole_0(B_2482))), inference(resolution, [status(thm)], [c_49598, c_30])).
% 13.64/6.31  tff(c_49612, plain, (![B_2482]: (B_2482='#skF_7' | ~v1_xboole_0(B_2482))), inference(demodulation, [status(thm), theory('equality')], [c_48812, c_49606])).
% 13.64/6.31  tff(c_52486, plain, (![C_2596]: (k2_zfmisc_1('#skF_7', C_2596)='#skF_7')), inference(resolution, [status(thm)], [c_52479, c_49612])).
% 13.64/6.31  tff(c_49070, plain, (![A_2436, C_2437, B_2438]: (r2_hidden(k2_mcart_1(A_2436), C_2437) | ~r2_hidden(A_2436, k2_zfmisc_1(B_2438, C_2437)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.64/6.31  tff(c_52280, plain, (![B_2585, C_2586]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_2585, C_2586))), C_2586) | v1_xboole_0(k2_zfmisc_1(B_2585, C_2586)))), inference(resolution, [status(thm)], [c_4, c_49070])).
% 13.64/6.31  tff(c_52319, plain, (![B_2587]: (v1_xboole_0(k2_zfmisc_1(B_2587, '#skF_7')))), inference(resolution, [status(thm)], [c_52280, c_48766])).
% 13.64/6.31  tff(c_52330, plain, (![B_2588]: (k2_zfmisc_1(B_2588, '#skF_7')='#skF_7')), inference(resolution, [status(thm)], [c_52319, c_49612])).
% 13.64/6.31  tff(c_52340, plain, (![B_2588, C_28]: (k3_zfmisc_1(B_2588, '#skF_7', C_28)=k2_zfmisc_1('#skF_7', C_28))), inference(superposition, [status(thm), theory('equality')], [c_52330, c_38])).
% 13.64/6.31  tff(c_52524, plain, (![B_2588, C_28]: (k3_zfmisc_1(B_2588, '#skF_7', C_28)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_52486, c_52340])).
% 13.64/6.31  tff(c_267, plain, (![A_78, A_21]: (r1_xboole_0(A_78, A_21) | ~r1_tarski(A_78, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_136, c_255])).
% 13.64/6.31  tff(c_49133, plain, (![A_78, A_21]: (r1_xboole_0(A_78, A_21) | ~r1_tarski(A_78, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_48797, c_267])).
% 13.64/6.31  tff(c_49166, plain, (![B_2447, C_2448]: (~r1_xboole_0(B_2447, B_2447) | ~r2_hidden(C_2448, B_2447))), inference(superposition, [status(thm), theory('equality')], [c_87, c_234])).
% 13.64/6.31  tff(c_49457, plain, (![C_2468, A_2469]: (~r2_hidden(C_2468, A_2469) | ~r1_tarski(A_2469, '#skF_7'))), inference(resolution, [status(thm)], [c_49133, c_49166])).
% 13.64/6.31  tff(c_49476, plain, (~r1_tarski(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_52, c_49457])).
% 13.64/6.31  tff(c_52525, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_52524, c_49476])).
% 13.64/6.31  tff(c_52532, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_52525])).
% 13.64/6.31  tff(c_52533, plain, (~r2_hidden(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_7') | ~r2_hidden(k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_50])).
% 13.64/6.31  tff(c_52599, plain, (~r2_hidden(k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_8')), inference(splitLeft, [status(thm)], [c_52533])).
% 13.64/6.31  tff(c_53635, plain, (~r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_53554, c_52599])).
% 13.64/6.31  tff(c_53316, plain, (![A_2651, C_2652, B_2653]: (r2_hidden(k2_mcart_1(A_2651), C_2652) | ~r2_hidden(A_2651, k2_zfmisc_1(B_2653, C_2652)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.64/6.31  tff(c_56209, plain, (![A_2763, C_2764, A_2765, B_2766]: (r2_hidden(k2_mcart_1(A_2763), C_2764) | ~r2_hidden(A_2763, k3_zfmisc_1(A_2765, B_2766, C_2764)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_53316])).
% 13.64/6.31  tff(c_56214, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_52, c_56209])).
% 13.64/6.31  tff(c_56222, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53635, c_56214])).
% 13.64/6.31  tff(c_56223, plain, (![C_2620]: (~r2_hidden(C_2620, '#skF_8'))), inference(splitRight, [status(thm)], [c_52838])).
% 13.64/6.31  tff(c_56310, plain, (![A_2768, C_2769, B_2770]: (r2_hidden(k2_mcart_1(A_2768), C_2769) | ~r2_hidden(A_2768, k2_zfmisc_1(B_2770, C_2769)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.64/6.31  tff(c_58437, plain, (![A_2868, C_2869, A_2870, B_2871]: (r2_hidden(k2_mcart_1(A_2868), C_2869) | ~r2_hidden(A_2868, k3_zfmisc_1(A_2870, B_2871, C_2869)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_56310])).
% 13.64/6.31  tff(c_58439, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_52, c_58437])).
% 13.64/6.31  tff(c_58446, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56223, c_58439])).
% 13.64/6.31  tff(c_58447, plain, (![C_2620]: (~r2_hidden(C_2620, '#skF_6'))), inference(splitRight, [status(thm)], [c_52841])).
% 13.64/6.31  tff(c_52534, plain, (r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_6')), inference(splitRight, [status(thm)], [c_50])).
% 13.64/6.31  tff(c_58450, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58447, c_52534])).
% 13.64/6.31  tff(c_58452, plain, (r1_xboole_0('#skF_7', '#skF_4')), inference(splitRight, [status(thm)], [c_52835])).
% 13.64/6.31  tff(c_58465, plain, (k4_xboole_0('#skF_7', '#skF_4')='#skF_7'), inference(resolution, [status(thm)], [c_58452, c_30])).
% 13.64/6.31  tff(c_52585, plain, (k4_xboole_0('#skF_7', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_52562, c_20])).
% 13.64/6.31  tff(c_58484, plain, (k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_58465, c_52585])).
% 13.64/6.31  tff(c_44, plain, (![A_32, B_33, C_34, D_36]: (k7_mcart_1(A_32, B_33, C_34, D_36)=k2_mcart_1(D_36) | ~m1_subset_1(D_36, k3_zfmisc_1(A_32, B_33, C_34)) | k1_xboole_0=C_34 | k1_xboole_0=B_33 | k1_xboole_0=A_32)), inference(cnfTransformation, [status(thm)], [f_107])).
% 13.64/6.31  tff(c_59271, plain, (![A_2918, B_2919, C_2920, D_2921]: (k7_mcart_1(A_2918, B_2919, C_2920, D_2921)=k2_mcart_1(D_2921) | ~m1_subset_1(D_2921, k3_zfmisc_1(A_2918, B_2919, C_2920)) | C_2920='#skF_7' | B_2919='#skF_7' | A_2918='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_58484, c_58484, c_58484, c_44])).
% 13.64/6.31  tff(c_59275, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')=k2_mcart_1('#skF_9') | '#skF_7'='#skF_5' | '#skF_7'='#skF_4' | '#skF_7'='#skF_3'), inference(resolution, [status(thm)], [c_54, c_59271])).
% 13.64/6.31  tff(c_59308, plain, ('#skF_7'='#skF_3'), inference(splitLeft, [status(thm)], [c_59275])).
% 13.64/6.31  tff(c_52577, plain, (k4_xboole_0('#skF_6', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_52561, c_20])).
% 13.64/6.31  tff(c_58538, plain, (k4_xboole_0('#skF_6', '#skF_3')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_58484, c_52577])).
% 13.64/6.31  tff(c_58636, plain, (![A_2878, C_2879, B_2880]: (r1_xboole_0(A_2878, C_2879) | ~r1_tarski(A_2878, k4_xboole_0(B_2880, C_2879)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.64/6.31  tff(c_59173, plain, (![A_2912]: (r1_xboole_0(A_2912, '#skF_3') | ~r1_tarski(A_2912, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_58538, c_58636])).
% 13.64/6.31  tff(c_58459, plain, (~r1_xboole_0('#skF_6', '#skF_3')), inference(splitLeft, [status(thm)], [c_52841])).
% 13.64/6.31  tff(c_59186, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_59173, c_58459])).
% 13.64/6.31  tff(c_59313, plain, (~r1_tarski('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_59308, c_59186])).
% 13.64/6.31  tff(c_59340, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52561, c_59313])).
% 13.64/6.31  tff(c_59341, plain, ('#skF_7'='#skF_4' | '#skF_7'='#skF_5' | k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')=k2_mcart_1('#skF_9')), inference(splitRight, [status(thm)], [c_59275])).
% 13.64/6.31  tff(c_59511, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')=k2_mcart_1('#skF_9')), inference(splitLeft, [status(thm)], [c_59341])).
% 13.64/6.31  tff(c_60605, plain, (~r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_59511, c_52599])).
% 13.64/6.31  tff(c_58941, plain, (![A_2901, B_2902, C_2903]: (k2_zfmisc_1(k2_zfmisc_1(A_2901, B_2902), C_2903)=k3_zfmisc_1(A_2901, B_2902, C_2903))), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.64/6.31  tff(c_60766, plain, (![A_2986, C_2987, A_2988, B_2989]: (r2_hidden(k2_mcart_1(A_2986), C_2987) | ~r2_hidden(A_2986, k3_zfmisc_1(A_2988, B_2989, C_2987)))), inference(superposition, [status(thm), theory('equality')], [c_58941, c_40])).
% 13.64/6.31  tff(c_60768, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_52, c_60766])).
% 13.64/6.31  tff(c_60775, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60605, c_60768])).
% 13.64/6.31  tff(c_60776, plain, ('#skF_7'='#skF_5' | '#skF_7'='#skF_4'), inference(splitRight, [status(thm)], [c_59341])).
% 13.64/6.31  tff(c_60778, plain, ('#skF_7'='#skF_4'), inference(splitLeft, [status(thm)], [c_60776])).
% 13.64/6.31  tff(c_58504, plain, (![B_2873, A_2874]: (B_2873=A_2874 | ~r1_tarski(B_2873, A_2874) | ~r1_tarski(A_2874, B_2873))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.64/6.31  tff(c_58523, plain, ('#skF_7'='#skF_4' | ~r1_tarski('#skF_4', '#skF_7')), inference(resolution, [status(thm)], [c_52562, c_58504])).
% 13.64/6.31  tff(c_58688, plain, (~r1_tarski('#skF_4', '#skF_7')), inference(splitLeft, [status(thm)], [c_58523])).
% 13.64/6.31  tff(c_60802, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60778, c_58688])).
% 13.64/6.31  tff(c_60818, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_60802])).
% 13.64/6.32  tff(c_60820, plain, ('#skF_7'!='#skF_4'), inference(splitRight, [status(thm)], [c_60776])).
% 13.64/6.32  tff(c_59342, plain, ('#skF_7'!='#skF_3'), inference(splitRight, [status(thm)], [c_59275])).
% 13.64/6.32  tff(c_48, plain, (![A_32, B_33, C_34, D_36]: (k5_mcart_1(A_32, B_33, C_34, D_36)=k1_mcart_1(k1_mcart_1(D_36)) | ~m1_subset_1(D_36, k3_zfmisc_1(A_32, B_33, C_34)) | k1_xboole_0=C_34 | k1_xboole_0=B_33 | k1_xboole_0=A_32)), inference(cnfTransformation, [status(thm)], [f_107])).
% 13.64/6.32  tff(c_59344, plain, (![A_2925, B_2926, C_2927, D_2928]: (k5_mcart_1(A_2925, B_2926, C_2927, D_2928)=k1_mcart_1(k1_mcart_1(D_2928)) | ~m1_subset_1(D_2928, k3_zfmisc_1(A_2925, B_2926, C_2927)) | C_2927='#skF_7' | B_2926='#skF_7' | A_2925='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_58484, c_58484, c_58484, c_48])).
% 13.64/6.32  tff(c_59347, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | '#skF_7'='#skF_5' | '#skF_7'='#skF_4' | '#skF_7'='#skF_3'), inference(resolution, [status(thm)], [c_54, c_59344])).
% 13.64/6.32  tff(c_59350, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | '#skF_7'='#skF_5' | '#skF_7'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_59342, c_59347])).
% 13.64/6.32  tff(c_60821, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | '#skF_7'='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_60820, c_59350])).
% 13.64/6.32  tff(c_60822, plain, ('#skF_7'='#skF_5'), inference(splitLeft, [status(thm)], [c_60821])).
% 13.64/6.32  tff(c_52629, plain, (![A_2605, B_2606, C_2607]: (r1_tarski(A_2605, B_2606) | ~r1_tarski(A_2605, k4_xboole_0(B_2606, C_2607)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.64/6.32  tff(c_52661, plain, (![B_2608, C_2609]: (r1_tarski(k4_xboole_0(B_2608, C_2609), B_2608))), inference(resolution, [status(thm)], [c_16, c_52629])).
% 13.64/6.32  tff(c_52688, plain, (![B_2608, C_2609]: (k4_xboole_0(k4_xboole_0(B_2608, C_2609), B_2608)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52661, c_20])).
% 13.64/6.32  tff(c_59032, plain, (![B_2906, C_2907]: (k4_xboole_0(k4_xboole_0(B_2906, C_2907), B_2906)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_58484, c_52688])).
% 13.64/6.32  tff(c_22, plain, (![A_16, C_18, B_17]: (r1_xboole_0(A_16, C_18) | ~r1_tarski(A_16, k4_xboole_0(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.64/6.32  tff(c_59250, plain, (![A_2916, B_2917]: (r1_xboole_0(A_2916, B_2917) | ~r1_tarski(A_2916, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_59032, c_22])).
% 13.64/6.32  tff(c_59288, plain, (![B_2923, A_2924]: (r1_xboole_0(B_2923, A_2924) | ~r1_tarski(A_2924, '#skF_7'))), inference(resolution, [status(thm)], [c_59250, c_6])).
% 13.64/6.32  tff(c_58931, plain, (~r1_xboole_0('#skF_8', '#skF_5')), inference(splitLeft, [status(thm)], [c_52838])).
% 13.64/6.32  tff(c_59303, plain, (~r1_tarski('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_59288, c_58931])).
% 13.64/6.32  tff(c_60832, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60822, c_59303])).
% 13.64/6.32  tff(c_60863, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_60832])).
% 13.64/6.32  tff(c_60865, plain, ('#skF_7'!='#skF_5'), inference(splitRight, [status(thm)], [c_60821])).
% 13.64/6.32  tff(c_60819, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_60776])).
% 13.64/6.32  tff(c_60866, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60865, c_60819])).
% 13.64/6.32  tff(c_60867, plain, (![C_2620]: (~r2_hidden(C_2620, '#skF_8'))), inference(splitRight, [status(thm)], [c_52838])).
% 13.64/6.32  tff(c_60868, plain, (r1_xboole_0('#skF_8', '#skF_5')), inference(splitRight, [status(thm)], [c_52838])).
% 13.64/6.32  tff(c_60899, plain, (k4_xboole_0('#skF_8', '#skF_5')='#skF_8'), inference(resolution, [status(thm)], [c_60868, c_30])).
% 13.64/6.32  tff(c_52569, plain, (k4_xboole_0('#skF_8', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_52560, c_20])).
% 13.64/6.32  tff(c_58537, plain, (k4_xboole_0('#skF_8', '#skF_5')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_58484, c_52569])).
% 13.64/6.32  tff(c_60909, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_60899, c_58537])).
% 13.64/6.32  tff(c_60953, plain, (r2_hidden('#skF_9', k3_zfmisc_1('#skF_6', '#skF_8', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_60909, c_52])).
% 13.64/6.32  tff(c_60875, plain, (![A_2991, B_2992, C_2993]: (k2_zfmisc_1(k2_zfmisc_1(A_2991, B_2992), C_2993)=k3_zfmisc_1(A_2991, B_2992, C_2993))), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.64/6.32  tff(c_62364, plain, (![A_3063, C_3064, A_3065, B_3066]: (r2_hidden(k2_mcart_1(A_3063), C_3064) | ~r2_hidden(A_3063, k3_zfmisc_1(A_3065, B_3066, C_3064)))), inference(superposition, [status(thm), theory('equality')], [c_60875, c_40])).
% 13.64/6.32  tff(c_62366, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_60953, c_62364])).
% 13.64/6.32  tff(c_62373, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60867, c_62366])).
% 13.64/6.32  tff(c_62374, plain, ('#skF_7'='#skF_4'), inference(splitRight, [status(thm)], [c_58523])).
% 13.64/6.32  tff(c_58451, plain, (![C_2620]: (~r2_hidden(C_2620, '#skF_7'))), inference(splitRight, [status(thm)], [c_52835])).
% 13.64/6.32  tff(c_62387, plain, (![C_2620]: (~r2_hidden(C_2620, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62374, c_58451])).
% 13.64/6.32  tff(c_62646, plain, (![A_3081, C_3082, B_3083]: (r2_hidden(k2_mcart_1(A_3081), C_3082) | ~r2_hidden(A_3081, k2_zfmisc_1(B_3083, C_3082)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.64/6.32  tff(c_64905, plain, (![B_3189, C_3190]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_3189, C_3190))), C_3190) | v1_xboole_0(k2_zfmisc_1(B_3189, C_3190)))), inference(resolution, [status(thm)], [c_4, c_62646])).
% 13.64/6.32  tff(c_58540, plain, (![B_13]: (k4_xboole_0(B_13, B_13)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_58484, c_135])).
% 13.64/6.32  tff(c_62378, plain, (![B_13]: (k4_xboole_0(B_13, B_13)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62374, c_58540])).
% 13.64/6.32  tff(c_62779, plain, (![B_3091, C_3092]: (~r1_xboole_0(B_3091, B_3091) | ~r2_hidden(C_3092, B_3091))), inference(superposition, [status(thm), theory('equality')], [c_87, c_52832])).
% 13.64/6.32  tff(c_62788, plain, (![C_3092, A_63]: (~r2_hidden(C_3092, A_63) | k4_xboole_0(A_63, A_63)!=A_63)), inference(resolution, [status(thm)], [c_123, c_62779])).
% 13.64/6.32  tff(c_62795, plain, (![C_3092, A_63]: (~r2_hidden(C_3092, A_63) | A_63!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62378, c_62788])).
% 13.64/6.32  tff(c_65058, plain, (![C_3200, B_3201]: (C_3200!='#skF_4' | v1_xboole_0(k2_zfmisc_1(B_3201, C_3200)))), inference(resolution, [status(thm)], [c_64905, c_62795])).
% 13.64/6.32  tff(c_62740, plain, (![A_3089, B_3090]: (r2_hidden('#skF_2'(A_3089, B_3090), k3_xboole_0(A_3089, B_3090)) | r1_xboole_0(A_3089, B_3090))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.64/6.32  tff(c_63112, plain, (![A_3119, B_3120]: (~v1_xboole_0(k3_xboole_0(A_3119, B_3120)) | r1_xboole_0(A_3119, B_3120))), inference(resolution, [status(thm)], [c_62740, c_2])).
% 13.64/6.32  tff(c_63133, plain, (![B_3121]: (~v1_xboole_0(B_3121) | r1_xboole_0(B_3121, B_3121))), inference(superposition, [status(thm), theory('equality')], [c_87, c_63112])).
% 13.64/6.32  tff(c_63138, plain, (![B_3121]: (k4_xboole_0(B_3121, B_3121)=B_3121 | ~v1_xboole_0(B_3121))), inference(resolution, [status(thm)], [c_63133, c_30])).
% 13.64/6.32  tff(c_63143, plain, (![B_3121]: (B_3121='#skF_4' | ~v1_xboole_0(B_3121))), inference(demodulation, [status(thm), theory('equality')], [c_62378, c_63138])).
% 13.64/6.32  tff(c_65274, plain, (![B_3201]: (k2_zfmisc_1(B_3201, '#skF_4')='#skF_4')), inference(resolution, [status(thm)], [c_65058, c_63143])).
% 13.64/6.32  tff(c_62389, plain, (r2_hidden('#skF_9', k3_zfmisc_1('#skF_6', '#skF_4', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_62374, c_52])).
% 13.64/6.32  tff(c_62565, plain, (![A_3077, B_3078, C_3079]: (r2_hidden(k1_mcart_1(A_3077), B_3078) | ~r2_hidden(A_3077, k2_zfmisc_1(B_3078, C_3079)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.64/6.32  tff(c_65330, plain, (![A_3218, A_3219, B_3220, C_3221]: (r2_hidden(k1_mcart_1(A_3218), k2_zfmisc_1(A_3219, B_3220)) | ~r2_hidden(A_3218, k3_zfmisc_1(A_3219, B_3220, C_3221)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_62565])).
% 13.64/6.32  tff(c_65342, plain, (r2_hidden(k1_mcart_1('#skF_9'), k2_zfmisc_1('#skF_6', '#skF_4'))), inference(resolution, [status(thm)], [c_62389, c_65330])).
% 13.64/6.32  tff(c_65351, plain, (r2_hidden(k1_mcart_1('#skF_9'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_65274, c_65342])).
% 13.64/6.32  tff(c_65353, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62387, c_65351])).
% 13.64/6.32  tff(c_65354, plain, (![C_2620]: (~r2_hidden(C_2620, '#skF_6'))), inference(splitRight, [status(thm)], [c_52841])).
% 13.64/6.32  tff(c_65364, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65354, c_52534])).
% 13.64/6.32  tff(c_65365, plain, (~r2_hidden(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_7')), inference(splitRight, [status(thm)], [c_52533])).
% 13.64/6.32  tff(c_65579, plain, (![A_3238, C_3239, B_3240]: (r1_xboole_0(A_3238, C_3239) | ~r1_tarski(A_3238, k4_xboole_0(B_3240, C_3239)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.64/6.32  tff(c_65623, plain, (![C_3241]: (r1_xboole_0(k1_xboole_0, C_3241))), inference(resolution, [status(thm)], [c_28, c_65579])).
% 13.64/6.32  tff(c_65632, plain, (![C_3242]: (r1_xboole_0(C_3242, k1_xboole_0))), inference(resolution, [status(thm)], [c_65623, c_6])).
% 13.64/6.32  tff(c_65638, plain, (![C_3242]: (k4_xboole_0(C_3242, k1_xboole_0)=C_3242)), inference(resolution, [status(thm)], [c_65632, c_30])).
% 13.64/6.32  tff(c_65785, plain, (![A_3249, A_3250]: (r1_xboole_0(A_3249, A_3250) | ~r1_tarski(A_3249, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_136, c_65579])).
% 13.64/6.32  tff(c_66154, plain, (![A_3274, A_3275]: (r1_xboole_0(A_3274, A_3275) | ~r1_tarski(A_3275, k1_xboole_0))), inference(resolution, [status(thm)], [c_65785, c_6])).
% 13.64/6.32  tff(c_65793, plain, (![A_3251, B_3252, C_3253]: (~r1_xboole_0(A_3251, B_3252) | ~r2_hidden(C_3253, k3_xboole_0(A_3251, B_3252)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.64/6.32  tff(c_65802, plain, (![C_3253]: (~r1_xboole_0('#skF_6', '#skF_3') | ~r2_hidden(C_3253, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_52578, c_65793])).
% 13.64/6.32  tff(c_66056, plain, (~r1_xboole_0('#skF_6', '#skF_3')), inference(splitLeft, [status(thm)], [c_65802])).
% 13.64/6.32  tff(c_66169, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_66154, c_66056])).
% 13.64/6.32  tff(c_66183, plain, (k4_xboole_0('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_66169])).
% 13.64/6.32  tff(c_66185, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_65638, c_66183])).
% 13.64/6.32  tff(c_65796, plain, (![C_3253]: (~r1_xboole_0('#skF_7', '#skF_4') | ~r2_hidden(C_3253, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_52586, c_65793])).
% 13.64/6.32  tff(c_65967, plain, (~r1_xboole_0('#skF_7', '#skF_4')), inference(splitLeft, [status(thm)], [c_65796])).
% 13.64/6.32  tff(c_66170, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_66154, c_65967])).
% 13.64/6.32  tff(c_66188, plain, (k4_xboole_0('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_66170])).
% 13.64/6.32  tff(c_66190, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_65638, c_66188])).
% 13.64/6.32  tff(c_65792, plain, (![A_3250, A_3249]: (r1_xboole_0(A_3250, A_3249) | ~r1_tarski(A_3249, k1_xboole_0))), inference(resolution, [status(thm)], [c_65785, c_6])).
% 13.64/6.32  tff(c_65799, plain, (![C_3253]: (~r1_xboole_0('#skF_8', '#skF_5') | ~r2_hidden(C_3253, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_52570, c_65793])).
% 13.64/6.32  tff(c_66191, plain, (~r1_xboole_0('#skF_8', '#skF_5')), inference(splitLeft, [status(thm)], [c_65799])).
% 13.64/6.32  tff(c_66204, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_65792, c_66191])).
% 13.64/6.32  tff(c_66211, plain, (k4_xboole_0('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_66204])).
% 13.64/6.32  tff(c_66213, plain, (k1_xboole_0!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_65638, c_66211])).
% 13.64/6.32  tff(c_67169, plain, (![A_3318, B_3319, C_3320, D_3321]: (k6_mcart_1(A_3318, B_3319, C_3320, D_3321)=k2_mcart_1(k1_mcart_1(D_3321)) | ~m1_subset_1(D_3321, k3_zfmisc_1(A_3318, B_3319, C_3320)) | k1_xboole_0=C_3320 | k1_xboole_0=B_3319 | k1_xboole_0=A_3318)), inference(cnfTransformation, [status(thm)], [f_107])).
% 13.64/6.32  tff(c_67172, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_54, c_67169])).
% 13.64/6.32  tff(c_67175, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_66185, c_66190, c_66213, c_67172])).
% 13.64/6.32  tff(c_66003, plain, (![A_3268, B_3269, C_3270]: (r2_hidden(k1_mcart_1(A_3268), B_3269) | ~r2_hidden(A_3268, k2_zfmisc_1(B_3269, C_3270)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.64/6.32  tff(c_70585, plain, (![A_3453, A_3454, B_3455, C_3456]: (r2_hidden(k1_mcart_1(A_3453), k2_zfmisc_1(A_3454, B_3455)) | ~r2_hidden(A_3453, k3_zfmisc_1(A_3454, B_3455, C_3456)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_66003])).
% 13.64/6.32  tff(c_70616, plain, (r2_hidden(k1_mcart_1('#skF_9'), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_52, c_70585])).
% 13.64/6.32  tff(c_70619, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')), '#skF_7')), inference(resolution, [status(thm)], [c_70616, c_40])).
% 13.64/6.32  tff(c_70638, plain, (r2_hidden(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_67175, c_70619])).
% 13.64/6.32  tff(c_70640, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65365, c_70638])).
% 13.64/6.32  tff(c_70641, plain, (![C_3253]: (~r2_hidden(C_3253, '#skF_8'))), inference(splitRight, [status(thm)], [c_65799])).
% 13.64/6.32  tff(c_65366, plain, (r2_hidden(k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_52533])).
% 13.64/6.32  tff(c_70644, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70641, c_65366])).
% 13.64/6.32  tff(c_70645, plain, (![C_3253]: (~r2_hidden(C_3253, '#skF_6'))), inference(splitRight, [status(thm)], [c_65802])).
% 13.64/6.32  tff(c_70649, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70645, c_52534])).
% 13.64/6.32  tff(c_70650, plain, (![C_3253]: (~r2_hidden(C_3253, '#skF_7'))), inference(splitRight, [status(thm)], [c_65796])).
% 13.64/6.32  tff(c_70651, plain, (r1_xboole_0('#skF_7', '#skF_4')), inference(splitRight, [status(thm)], [c_65796])).
% 13.64/6.32  tff(c_70663, plain, (k4_xboole_0('#skF_7', '#skF_4')='#skF_7'), inference(resolution, [status(thm)], [c_70651, c_30])).
% 13.64/6.32  tff(c_70680, plain, (k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_70663, c_52585])).
% 13.64/6.32  tff(c_32, plain, (![A_22, B_23]: (r1_xboole_0(A_22, B_23) | k4_xboole_0(A_22, B_23)!=A_22)), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.64/6.32  tff(c_65822, plain, (![B_3255, C_3256]: (~r1_xboole_0(B_3255, B_3255) | ~r2_hidden(C_3256, B_3255))), inference(superposition, [status(thm), theory('equality')], [c_87, c_65793])).
% 13.64/6.32  tff(c_65837, plain, (![C_3256, B_23]: (~r2_hidden(C_3256, B_23) | k4_xboole_0(B_23, B_23)!=B_23)), inference(resolution, [status(thm)], [c_32, c_65822])).
% 13.64/6.32  tff(c_65846, plain, (![C_3257, B_3258]: (~r2_hidden(C_3257, B_3258) | k1_xboole_0!=B_3258)), inference(demodulation, [status(thm), theory('equality')], [c_135, c_65837])).
% 13.64/6.32  tff(c_65862, plain, (![A_1]: (k1_xboole_0!=A_1 | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_65846])).
% 13.64/6.32  tff(c_70716, plain, (![A_1]: (A_1!='#skF_7' | v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_70680, c_65862])).
% 13.64/6.32  tff(c_70787, plain, (![A_3464, C_3465, B_3466]: (r2_hidden(k2_mcart_1(A_3464), C_3465) | ~r2_hidden(A_3464, k2_zfmisc_1(B_3466, C_3465)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.64/6.32  tff(c_73487, plain, (![B_3592, C_3593]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_3592, C_3593))), C_3593) | v1_xboole_0(k2_zfmisc_1(B_3592, C_3593)))), inference(resolution, [status(thm)], [c_4, c_70787])).
% 13.64/6.32  tff(c_73596, plain, (![C_3600, B_3601]: (~v1_xboole_0(C_3600) | v1_xboole_0(k2_zfmisc_1(B_3601, C_3600)))), inference(resolution, [status(thm)], [c_73487, c_2])).
% 13.64/6.32  tff(c_70730, plain, (![B_13]: (k4_xboole_0(B_13, B_13)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70680, c_135])).
% 13.64/6.32  tff(c_71010, plain, (![A_3472, B_3473]: (r2_hidden('#skF_2'(A_3472, B_3473), k3_xboole_0(A_3472, B_3473)) | r1_xboole_0(A_3472, B_3473))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.64/6.32  tff(c_71486, plain, (![A_3506, B_3507]: (~v1_xboole_0(k3_xboole_0(A_3506, B_3507)) | r1_xboole_0(A_3506, B_3507))), inference(resolution, [status(thm)], [c_71010, c_2])).
% 13.64/6.32  tff(c_71507, plain, (![B_3508]: (~v1_xboole_0(B_3508) | r1_xboole_0(B_3508, B_3508))), inference(superposition, [status(thm), theory('equality')], [c_87, c_71486])).
% 13.64/6.32  tff(c_71512, plain, (![B_3508]: (k4_xboole_0(B_3508, B_3508)=B_3508 | ~v1_xboole_0(B_3508))), inference(resolution, [status(thm)], [c_71507, c_30])).
% 13.64/6.32  tff(c_71517, plain, (![B_3508]: (B_3508='#skF_7' | ~v1_xboole_0(B_3508))), inference(demodulation, [status(thm), theory('equality')], [c_70730, c_71512])).
% 13.64/6.32  tff(c_73623, plain, (![B_3604, C_3605]: (k2_zfmisc_1(B_3604, C_3605)='#skF_7' | ~v1_xboole_0(C_3605))), inference(resolution, [status(thm)], [c_73596, c_71517])).
% 13.64/6.32  tff(c_73836, plain, (![B_3604]: (k2_zfmisc_1(B_3604, '#skF_7')='#skF_7')), inference(resolution, [status(thm)], [c_70716, c_73623])).
% 13.64/6.32  tff(c_70673, plain, (![A_3458, B_3459, C_3460]: (r2_hidden(k1_mcart_1(A_3458), B_3459) | ~r2_hidden(A_3458, k2_zfmisc_1(B_3459, C_3460)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.64/6.32  tff(c_73892, plain, (![A_3620, A_3621, B_3622, C_3623]: (r2_hidden(k1_mcart_1(A_3620), k2_zfmisc_1(A_3621, B_3622)) | ~r2_hidden(A_3620, k3_zfmisc_1(A_3621, B_3622, C_3623)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_70673])).
% 13.64/6.32  tff(c_73904, plain, (r2_hidden(k1_mcart_1('#skF_9'), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_52, c_73892])).
% 13.64/6.32  tff(c_73913, plain, (r2_hidden(k1_mcart_1('#skF_9'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_73836, c_73904])).
% 13.64/6.32  tff(c_73915, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70650, c_73913])).
% 13.64/6.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.64/6.32  
% 13.64/6.32  Inference rules
% 13.64/6.32  ----------------------
% 13.64/6.32  #Ref     : 16
% 13.64/6.32  #Sup     : 17778
% 13.64/6.32  #Fact    : 0
% 13.64/6.32  #Define  : 0
% 13.64/6.32  #Split   : 71
% 13.64/6.32  #Chain   : 0
% 13.64/6.32  #Close   : 0
% 13.64/6.32  
% 13.64/6.32  Ordering : KBO
% 13.64/6.32  
% 13.64/6.32  Simplification rules
% 13.64/6.32  ----------------------
% 13.64/6.32  #Subsume      : 5340
% 13.64/6.32  #Demod        : 9707
% 13.64/6.32  #Tautology    : 9220
% 13.64/6.32  #SimpNegUnit  : 703
% 13.64/6.32  #BackRed      : 846
% 13.64/6.32  
% 13.64/6.32  #Partial instantiations: 0
% 13.64/6.32  #Strategies tried      : 1
% 13.64/6.32  
% 13.64/6.32  Timing (in seconds)
% 13.64/6.32  ----------------------
% 13.64/6.32  Preprocessing        : 0.35
% 13.64/6.32  Parsing              : 0.19
% 13.64/6.32  CNF conversion       : 0.03
% 13.64/6.32  Main loop            : 4.99
% 13.64/6.32  Inferencing          : 1.40
% 13.64/6.32  Reduction            : 2.06
% 13.64/6.32  Demodulation         : 1.46
% 13.64/6.32  BG Simplification    : 0.11
% 13.64/6.32  Subsumption          : 1.06
% 13.64/6.32  Abstraction          : 0.17
% 13.64/6.32  MUC search           : 0.00
% 13.64/6.32  Cooper               : 0.00
% 13.64/6.32  Total                : 5.53
% 13.64/6.32  Index Insertion      : 0.00
% 13.64/6.32  Index Deletion       : 0.00
% 13.64/6.32  Index Matching       : 0.00
% 13.64/6.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
