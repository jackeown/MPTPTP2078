%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:11 EST 2020

% Result     : Theorem 7.04s
% Output     : CNFRefutation 7.36s
% Verified   : 
% Statistics : Number of formulae       :  325 (1070 expanded)
%              Number of leaves         :   38 ( 359 expanded)
%              Depth                    :   13
%              Number of atoms          :  503 (2724 expanded)
%              Number of equality atoms :  142 ( 690 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_64,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_110,negated_conjecture,(
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

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_90,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_58,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_24,plain,(
    ! [A_20,B_21,C_22] : k2_zfmisc_1(k2_zfmisc_1(A_20,B_21),C_22) = k3_zfmisc_1(A_20,B_21,C_22) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_11635,plain,(
    ! [A_1054,B_1055,C_1056] :
      ( r2_hidden(k1_mcart_1(A_1054),B_1055)
      | ~ r2_hidden(A_1054,k2_zfmisc_1(B_1055,C_1056)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_11645,plain,(
    ! [B_1055,C_1056] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_1055,C_1056))),B_1055)
      | v1_xboole_0(k2_zfmisc_1(B_1055,C_1056)) ) ),
    inference(resolution,[status(thm)],[c_4,c_11635])).

tff(c_11760,plain,(
    ! [A_1073,C_1074,B_1075] :
      ( r2_hidden(k2_mcart_1(A_1073),C_1074)
      | ~ r2_hidden(A_1073,k2_zfmisc_1(B_1075,C_1074)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_12592,plain,(
    ! [B_1125,C_1126] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_1125,C_1126))),C_1126)
      | v1_xboole_0(k2_zfmisc_1(B_1125,C_1126)) ) ),
    inference(resolution,[status(thm)],[c_4,c_11760])).

tff(c_7795,plain,(
    ! [A_726,B_727,C_728] :
      ( r2_hidden(k1_mcart_1(A_726),B_727)
      | ~ r2_hidden(A_726,k2_zfmisc_1(B_727,C_728)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_7803,plain,(
    ! [B_727,C_728] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_727,C_728))),B_727)
      | v1_xboole_0(k2_zfmisc_1(B_727,C_728)) ) ),
    inference(resolution,[status(thm)],[c_4,c_7795])).

tff(c_7810,plain,(
    ! [A_731,C_732,B_733] :
      ( r2_hidden(k2_mcart_1(A_731),C_732)
      | ~ r2_hidden(A_731,k2_zfmisc_1(B_733,C_732)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_9083,plain,(
    ! [B_824,C_825] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_824,C_825))),C_825)
      | v1_xboole_0(k2_zfmisc_1(B_824,C_825)) ) ),
    inference(resolution,[status(thm)],[c_4,c_7810])).

tff(c_42,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_5669,plain,(
    ! [A_536,B_537] :
      ( r1_tarski(A_536,B_537)
      | ~ m1_subset_1(A_536,k1_zfmisc_1(B_537)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_5679,plain,(
    r1_tarski('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_5669])).

tff(c_44,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_5681,plain,(
    r1_tarski('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_5669])).

tff(c_38,plain,(
    r2_hidden('#skF_10',k3_zfmisc_1('#skF_7','#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_5913,plain,(
    ! [A_577,C_578,B_579] :
      ( r2_hidden(k2_mcart_1(A_577),C_578)
      | ~ r2_hidden(A_577,k2_zfmisc_1(B_579,C_578)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6499,plain,(
    ! [A_623,C_624,A_625,B_626] :
      ( r2_hidden(k2_mcart_1(A_623),C_624)
      | ~ r2_hidden(A_623,k3_zfmisc_1(A_625,B_626,C_624)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_5913])).

tff(c_6534,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_38,c_6499])).

tff(c_46,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_5680,plain,(
    r1_tarski('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_5669])).

tff(c_40,plain,(
    m1_subset_1('#skF_10',k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_6146,plain,(
    ! [A_594,B_595,C_596,D_597] :
      ( k7_mcart_1(A_594,B_595,C_596,D_597) = k2_mcart_1(D_597)
      | ~ m1_subset_1(D_597,k3_zfmisc_1(A_594,B_595,C_596))
      | k1_xboole_0 = C_596
      | k1_xboole_0 = B_595
      | k1_xboole_0 = A_594 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_6150,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_6146])).

tff(c_6211,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_6150])).

tff(c_3517,plain,(
    ! [A_348,B_349,C_350] :
      ( r2_hidden(k1_mcart_1(A_348),B_349)
      | ~ r2_hidden(A_348,k2_zfmisc_1(B_349,C_350)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3525,plain,(
    ! [B_349,C_350] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_349,C_350))),B_349)
      | v1_xboole_0(k2_zfmisc_1(B_349,C_350)) ) ),
    inference(resolution,[status(thm)],[c_4,c_3517])).

tff(c_4574,plain,(
    ! [B_441,C_442] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_441,C_442))),B_441)
      | v1_xboole_0(k2_zfmisc_1(B_441,C_442)) ) ),
    inference(resolution,[status(thm)],[c_4,c_3517])).

tff(c_36,plain,
    ( ~ r2_hidden(k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_9')
    | ~ r2_hidden(k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_8')
    | ~ r2_hidden(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_58,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_59,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | ~ m1_subset_1(A_46,k1_zfmisc_1(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_69,plain,(
    r1_tarski('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_59])).

tff(c_71,plain,(
    r1_tarski('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_59])).

tff(c_70,plain,(
    r1_tarski('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_59])).

tff(c_295,plain,(
    ! [C_87,B_88,A_89] :
      ( r2_hidden(C_87,B_88)
      | ~ r2_hidden(C_87,A_89)
      | ~ r1_tarski(A_89,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_305,plain,(
    ! [A_90,B_91] :
      ( r2_hidden('#skF_1'(A_90),B_91)
      | ~ r1_tarski(A_90,B_91)
      | v1_xboole_0(A_90) ) ),
    inference(resolution,[status(thm)],[c_4,c_295])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_366,plain,(
    ! [B_94,A_95] :
      ( ~ v1_xboole_0(B_94)
      | ~ r1_tarski(A_95,B_94)
      | v1_xboole_0(A_95) ) ),
    inference(resolution,[status(thm)],[c_305,c_2])).

tff(c_394,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_366])).

tff(c_397,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_394])).

tff(c_467,plain,(
    ! [A_99,B_100,C_101,D_102] :
      ( k7_mcart_1(A_99,B_100,C_101,D_102) = k2_mcart_1(D_102)
      | ~ m1_subset_1(D_102,k3_zfmisc_1(A_99,B_100,C_101))
      | k1_xboole_0 = C_101
      | k1_xboole_0 = B_100
      | k1_xboole_0 = A_99 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_471,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_467])).

tff(c_535,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_471])).

tff(c_18,plain,(
    ! [A_17] : r1_xboole_0(A_17,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_113,plain,(
    ! [A_58,B_59] :
      ( ~ r2_hidden('#skF_2'(A_58,B_59),B_59)
      | r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_119,plain,(
    ! [A_60] : r1_tarski(A_60,A_60) ),
    inference(resolution,[status(thm)],[c_10,c_113])).

tff(c_16,plain,(
    ! [A_15,B_16] :
      ( k3_xboole_0(A_15,B_16) = A_15
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_144,plain,(
    ! [A_64] : k3_xboole_0(A_64,A_64) = A_64 ),
    inference(resolution,[status(thm)],[c_119,c_16])).

tff(c_14,plain,(
    ! [A_10,B_11,C_14] :
      ( ~ r1_xboole_0(A_10,B_11)
      | ~ r2_hidden(C_14,k3_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_159,plain,(
    ! [A_65,C_66] :
      ( ~ r1_xboole_0(A_65,A_65)
      | ~ r2_hidden(C_66,A_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_14])).

tff(c_164,plain,(
    ! [C_67] : ~ r2_hidden(C_67,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_159])).

tff(c_174,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_164])).

tff(c_541,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_535,c_174])).

tff(c_545,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_397,c_541])).

tff(c_547,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_471])).

tff(c_719,plain,(
    ! [A_119,B_120,C_121,D_122] :
      ( k6_mcart_1(A_119,B_120,C_121,D_122) = k2_mcart_1(k1_mcart_1(D_122))
      | ~ m1_subset_1(D_122,k3_zfmisc_1(A_119,B_120,C_121))
      | k1_xboole_0 = C_121
      | k1_xboole_0 = B_120
      | k1_xboole_0 = A_119 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_722,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_719])).

tff(c_725,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_547,c_722])).

tff(c_780,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_725])).

tff(c_72,plain,(
    ! [A_48,B_49] :
      ( k3_xboole_0(A_48,B_49) = A_48
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_82,plain,(
    k3_xboole_0('#skF_8','#skF_5') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_71,c_72])).

tff(c_124,plain,(
    ! [A_61,B_62,C_63] :
      ( ~ r1_xboole_0(A_61,B_62)
      | ~ r2_hidden(C_63,k3_xboole_0(A_61,B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_137,plain,(
    ! [C_63] :
      ( ~ r1_xboole_0('#skF_8','#skF_5')
      | ~ r2_hidden(C_63,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_124])).

tff(c_158,plain,(
    ~ r1_xboole_0('#skF_8','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_398,plain,(
    ! [A_96,B_97] :
      ( r2_hidden('#skF_3'(A_96,B_97),k3_xboole_0(A_96,B_97))
      | r1_xboole_0(A_96,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_421,plain,
    ( r2_hidden('#skF_3'('#skF_8','#skF_5'),'#skF_8')
    | r1_xboole_0('#skF_8','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_398])).

tff(c_428,plain,(
    r2_hidden('#skF_3'('#skF_8','#skF_5'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_158,c_421])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_600,plain,(
    ! [B_113] :
      ( r2_hidden('#skF_3'('#skF_8','#skF_5'),B_113)
      | ~ r1_tarski('#skF_8',B_113) ) ),
    inference(resolution,[status(thm)],[c_428,c_6])).

tff(c_163,plain,(
    ! [C_66] : ~ r2_hidden(C_66,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_159])).

tff(c_623,plain,(
    ~ r1_tarski('#skF_8',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_600,c_163])).

tff(c_783,plain,(
    ~ r1_tarski('#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_780,c_623])).

tff(c_797,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_783])).

tff(c_799,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_725])).

tff(c_593,plain,(
    ! [A_109,B_110,C_111,D_112] :
      ( k5_mcart_1(A_109,B_110,C_111,D_112) = k1_mcart_1(k1_mcart_1(D_112))
      | ~ m1_subset_1(D_112,k3_zfmisc_1(A_109,B_110,C_111))
      | k1_xboole_0 = C_111
      | k1_xboole_0 = B_110
      | k1_xboole_0 = A_109 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_596,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_593])).

tff(c_599,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_547,c_596])).

tff(c_913,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_799,c_599])).

tff(c_914,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_913])).

tff(c_84,plain,(
    k3_xboole_0('#skF_9','#skF_6') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_69,c_72])).

tff(c_131,plain,(
    ! [C_63] :
      ( ~ r1_xboole_0('#skF_9','#skF_6')
      | ~ r2_hidden(C_63,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_124])).

tff(c_156,plain,(
    ~ r1_xboole_0('#skF_9','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_131])).

tff(c_415,plain,
    ( r2_hidden('#skF_3'('#skF_9','#skF_6'),'#skF_9')
    | r1_xboole_0('#skF_9','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_398])).

tff(c_426,plain,(
    r2_hidden('#skF_3'('#skF_9','#skF_6'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_415])).

tff(c_650,plain,(
    ! [B_115] :
      ( r2_hidden('#skF_3'('#skF_9','#skF_6'),B_115)
      | ~ r1_tarski('#skF_9',B_115) ) ),
    inference(resolution,[status(thm)],[c_426,c_6])).

tff(c_673,plain,(
    ~ r1_tarski('#skF_9',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_650,c_163])).

tff(c_917,plain,(
    ~ r1_tarski('#skF_9','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_914,c_673])).

tff(c_932,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_917])).

tff(c_933,plain,(
    k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') ),
    inference(splitRight,[status(thm)],[c_913])).

tff(c_212,plain,(
    ! [A_73,B_74,C_75] : k2_zfmisc_1(k2_zfmisc_1(A_73,B_74),C_75) = k3_zfmisc_1(A_73,B_74,C_75) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_28,plain,(
    ! [A_23,B_24,C_25] :
      ( r2_hidden(k1_mcart_1(A_23),B_24)
      | ~ r2_hidden(A_23,k2_zfmisc_1(B_24,C_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1682,plain,(
    ! [A_202,A_203,B_204,C_205] :
      ( r2_hidden(k1_mcart_1(A_202),k2_zfmisc_1(A_203,B_204))
      | ~ r2_hidden(A_202,k3_zfmisc_1(A_203,B_204,C_205)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_28])).

tff(c_1732,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_38,c_1682])).

tff(c_1738,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_1732,c_28])).

tff(c_1746,plain,(
    r2_hidden(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_933,c_1738])).

tff(c_1748,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1746])).

tff(c_1749,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_394])).

tff(c_102,plain,(
    ! [A_52,B_53] :
      ( r2_hidden('#skF_2'(A_52,B_53),A_52)
      | r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_107,plain,(
    ! [A_54,B_55] :
      ( ~ v1_xboole_0(A_54)
      | r1_tarski(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_102,c_2])).

tff(c_111,plain,(
    ! [A_54,B_55] :
      ( k3_xboole_0(A_54,B_55) = A_54
      | ~ v1_xboole_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_107,c_16])).

tff(c_1753,plain,(
    ! [B_55] : k3_xboole_0('#skF_7',B_55) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1749,c_111])).

tff(c_1821,plain,(
    ! [A_209,B_210] :
      ( r2_hidden('#skF_3'(A_209,B_210),k3_xboole_0(A_209,B_210))
      | r1_xboole_0(A_209,B_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2060,plain,(
    ! [A_226,B_227] :
      ( ~ v1_xboole_0(k3_xboole_0(A_226,B_227))
      | r1_xboole_0(A_226,B_227) ) ),
    inference(resolution,[status(thm)],[c_1821,c_2])).

tff(c_2063,plain,(
    ! [B_55] :
      ( ~ v1_xboole_0('#skF_7')
      | r1_xboole_0('#skF_7',B_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1753,c_2060])).

tff(c_2083,plain,(
    ! [B_55] : r1_xboole_0('#skF_7',B_55) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1749,c_2063])).

tff(c_83,plain,(
    k3_xboole_0('#skF_7','#skF_4') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_70,c_72])).

tff(c_134,plain,(
    ! [C_63] :
      ( ~ r1_xboole_0('#skF_7','#skF_4')
      | ~ r2_hidden(C_63,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_124])).

tff(c_157,plain,(
    ~ r1_xboole_0('#skF_7','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_2093,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2083,c_157])).

tff(c_2094,plain,(
    ! [C_63] : ~ r2_hidden(C_63,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_2252,plain,(
    ! [A_248,B_249,C_250] : k2_zfmisc_1(k2_zfmisc_1(A_248,B_249),C_250) = k3_zfmisc_1(A_248,B_249,C_250) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3411,plain,(
    ! [A_341,A_342,B_343,C_344] :
      ( r2_hidden(k1_mcart_1(A_341),k2_zfmisc_1(A_342,B_343))
      | ~ r2_hidden(A_341,k3_zfmisc_1(A_342,B_343,C_344)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2252,c_28])).

tff(c_3458,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_38,c_3411])).

tff(c_26,plain,(
    ! [A_23,C_25,B_24] :
      ( r2_hidden(k2_mcart_1(A_23),C_25)
      | ~ r2_hidden(A_23,k2_zfmisc_1(B_24,C_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3460,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')),'#skF_8') ),
    inference(resolution,[status(thm)],[c_3458,c_26])).

tff(c_3471,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2094,c_3460])).

tff(c_3472,plain,(
    ! [C_63] : ~ r2_hidden(C_63,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_4611,plain,(
    ! [C_442] : v1_xboole_0(k2_zfmisc_1('#skF_7',C_442)) ),
    inference(resolution,[status(thm)],[c_4574,c_3472])).

tff(c_4615,plain,(
    ! [C_443] : v1_xboole_0(k2_zfmisc_1('#skF_7',C_443)) ),
    inference(resolution,[status(thm)],[c_4574,c_3472])).

tff(c_4691,plain,(
    ! [C_451,B_452] : k3_xboole_0(k2_zfmisc_1('#skF_7',C_451),B_452) = k2_zfmisc_1('#skF_7',C_451) ),
    inference(resolution,[status(thm)],[c_4615,c_111])).

tff(c_3798,plain,(
    ! [A_380,B_381] :
      ( r2_hidden('#skF_3'(A_380,B_381),k3_xboole_0(A_380,B_381))
      | r1_xboole_0(A_380,B_381) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3824,plain,(
    ! [A_380,B_381] :
      ( ~ v1_xboole_0(k3_xboole_0(A_380,B_381))
      | r1_xboole_0(A_380,B_381) ) ),
    inference(resolution,[status(thm)],[c_3798,c_2])).

tff(c_4706,plain,(
    ! [C_451,B_452] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_7',C_451))
      | r1_xboole_0(k2_zfmisc_1('#skF_7',C_451),B_452) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4691,c_3824])).

tff(c_4777,plain,(
    ! [C_456,B_457] : r1_xboole_0(k2_zfmisc_1('#skF_7',C_456),B_457) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4611,c_4706])).

tff(c_150,plain,(
    ! [A_64,C_14] :
      ( ~ r1_xboole_0(A_64,A_64)
      | ~ r2_hidden(C_14,A_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_14])).

tff(c_4850,plain,(
    ! [C_463,C_464] : ~ r2_hidden(C_463,k2_zfmisc_1('#skF_7',C_464)) ),
    inference(resolution,[status(thm)],[c_4777,c_150])).

tff(c_4862,plain,(
    ! [C_464,C_350] : v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1('#skF_7',C_464),C_350)) ),
    inference(resolution,[status(thm)],[c_3525,c_4850])).

tff(c_4898,plain,(
    ! [C_464,C_350] : v1_xboole_0(k3_zfmisc_1('#skF_7',C_464,C_350)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_4862])).

tff(c_52,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_7','#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_38,c_2])).

tff(c_4922,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4898,c_52])).

tff(c_4923,plain,(
    ! [C_63] : ~ r2_hidden(C_63,'#skF_9') ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_5090,plain,(
    ! [A_487,C_488,B_489] :
      ( r2_hidden(k2_mcart_1(A_487),C_488)
      | ~ r2_hidden(A_487,k2_zfmisc_1(B_489,C_488)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_5636,plain,(
    ! [A_532,C_533,A_534,B_535] :
      ( r2_hidden(k2_mcart_1(A_532),C_533)
      | ~ r2_hidden(A_532,k3_zfmisc_1(A_534,B_535,C_533)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_5090])).

tff(c_5656,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_38,c_5636])).

tff(c_5666,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4923,c_5656])).

tff(c_5668,plain,(
    r2_hidden(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_5900,plain,(
    ! [C_574,B_575,A_576] :
      ( r2_hidden(C_574,B_575)
      | ~ r2_hidden(C_574,A_576)
      | ~ r1_tarski(A_576,B_575) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_5936,plain,(
    ! [B_581] :
      ( r2_hidden(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),B_581)
      | ~ r1_tarski('#skF_7',B_581) ) ),
    inference(resolution,[status(thm)],[c_5668,c_5900])).

tff(c_5734,plain,(
    ! [A_547,B_548] :
      ( r2_hidden('#skF_2'(A_547,B_548),A_547)
      | r1_tarski(A_547,B_548) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_5749,plain,(
    ! [A_549] : r1_tarski(A_549,A_549) ),
    inference(resolution,[status(thm)],[c_5734,c_8])).

tff(c_5754,plain,(
    ! [A_550] : k3_xboole_0(A_550,A_550) = A_550 ),
    inference(resolution,[status(thm)],[c_5749,c_16])).

tff(c_5773,plain,(
    ! [A_555,C_556] :
      ( ~ r1_xboole_0(A_555,A_555)
      | ~ r2_hidden(C_556,A_555) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5754,c_14])).

tff(c_5777,plain,(
    ! [C_556] : ~ r2_hidden(C_556,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_5773])).

tff(c_5959,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_5936,c_5777])).

tff(c_6214,plain,(
    ~ r1_tarski('#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6211,c_5959])).

tff(c_6222,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5680,c_6214])).

tff(c_6223,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_6'
    | k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_6150])).

tff(c_6867,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_6223])).

tff(c_5667,plain,
    ( ~ r2_hidden(k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_8')
    | ~ r2_hidden(k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_5716,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_5667])).

tff(c_6922,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6867,c_5716])).

tff(c_6925,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6534,c_6922])).

tff(c_6926,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_6223])).

tff(c_6928,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_6926])).

tff(c_5687,plain,(
    ! [A_540,B_541] :
      ( k3_xboole_0(A_540,B_541) = A_540
      | ~ r1_tarski(A_540,B_541) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_5698,plain,(
    k3_xboole_0('#skF_8','#skF_5') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_5681,c_5687])).

tff(c_5718,plain,(
    ! [A_544,B_545,C_546] :
      ( ~ r1_xboole_0(A_544,B_545)
      | ~ r2_hidden(C_546,k3_xboole_0(A_544,B_545)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_5721,plain,(
    ! [C_546] :
      ( ~ r1_xboole_0('#skF_8','#skF_5')
      | ~ r2_hidden(C_546,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5698,c_5718])).

tff(c_5733,plain,(
    ~ r1_xboole_0('#skF_8','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_5721])).

tff(c_6009,plain,(
    ! [A_586,B_587] :
      ( r2_hidden('#skF_3'(A_586,B_587),k3_xboole_0(A_586,B_587))
      | r1_xboole_0(A_586,B_587) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6026,plain,
    ( r2_hidden('#skF_3'('#skF_8','#skF_5'),'#skF_8')
    | r1_xboole_0('#skF_8','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5698,c_6009])).

tff(c_6037,plain,(
    r2_hidden('#skF_3'('#skF_8','#skF_5'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_5733,c_6026])).

tff(c_6277,plain,(
    ! [B_606] :
      ( r2_hidden('#skF_3'('#skF_8','#skF_5'),B_606)
      | ~ r1_tarski('#skF_8',B_606) ) ),
    inference(resolution,[status(thm)],[c_6037,c_6])).

tff(c_6300,plain,(
    ~ r1_tarski('#skF_8',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6277,c_5777])).

tff(c_6940,plain,(
    ~ r1_tarski('#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6928,c_6300])).

tff(c_6954,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5681,c_6940])).

tff(c_6956,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_6926])).

tff(c_6224,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6150])).

tff(c_6270,plain,(
    ! [A_602,B_603,C_604,D_605] :
      ( k5_mcart_1(A_602,B_603,C_604,D_605) = k1_mcart_1(k1_mcart_1(D_605))
      | ~ m1_subset_1(D_605,k3_zfmisc_1(A_602,B_603,C_604))
      | k1_xboole_0 = C_604
      | k1_xboole_0 = B_603
      | k1_xboole_0 = A_602 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_6273,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_6270])).

tff(c_6276,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_6224,c_6273])).

tff(c_6957,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_6956,c_6276])).

tff(c_6958,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_6957])).

tff(c_5699,plain,(
    k3_xboole_0('#skF_9','#skF_6') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_5679,c_5687])).

tff(c_5724,plain,(
    ! [C_546] :
      ( ~ r1_xboole_0('#skF_9','#skF_6')
      | ~ r2_hidden(C_546,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5699,c_5718])).

tff(c_5827,plain,(
    ~ r1_xboole_0('#skF_9','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_5724])).

tff(c_6029,plain,
    ( r2_hidden('#skF_3'('#skF_9','#skF_6'),'#skF_9')
    | r1_xboole_0('#skF_9','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_5699,c_6009])).

tff(c_6038,plain,(
    r2_hidden('#skF_3'('#skF_9','#skF_6'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_5827,c_6029])).

tff(c_6225,plain,(
    ! [B_600] :
      ( r2_hidden('#skF_3'('#skF_9','#skF_6'),B_600)
      | ~ r1_tarski('#skF_9',B_600) ) ),
    inference(resolution,[status(thm)],[c_6038,c_6])).

tff(c_6248,plain,(
    ~ r1_tarski('#skF_9',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6225,c_5777])).

tff(c_6973,plain,(
    ~ r1_tarski('#skF_9','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6958,c_6248])).

tff(c_6985,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5679,c_6973])).

tff(c_6987,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_6957])).

tff(c_6955,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_6926])).

tff(c_6988,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6987,c_6955])).

tff(c_6989,plain,(
    ! [C_546] : ~ r2_hidden(C_546,'#skF_9') ),
    inference(splitRight,[status(thm)],[c_5724])).

tff(c_7124,plain,(
    ! [A_675,B_676,C_677] : k2_zfmisc_1(k2_zfmisc_1(A_675,B_676),C_677) = k3_zfmisc_1(A_675,B_676,C_677) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_7677,plain,(
    ! [A_711,C_712,A_713,B_714] :
      ( r2_hidden(k2_mcart_1(A_711),C_712)
      | ~ r2_hidden(A_711,k3_zfmisc_1(A_713,B_714,C_712)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7124,c_26])).

tff(c_7700,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_38,c_7677])).

tff(c_7711,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6989,c_7700])).

tff(c_7712,plain,(
    ! [C_546] : ~ r2_hidden(C_546,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_5721])).

tff(c_9118,plain,(
    ! [B_824] : v1_xboole_0(k2_zfmisc_1(B_824,'#skF_8')) ),
    inference(resolution,[status(thm)],[c_9083,c_7712])).

tff(c_9122,plain,(
    ! [B_826] : v1_xboole_0(k2_zfmisc_1(B_826,'#skF_8')) ),
    inference(resolution,[status(thm)],[c_9083,c_7712])).

tff(c_7720,plain,(
    ! [A_716,B_717] :
      ( r2_hidden('#skF_2'(A_716,B_717),A_716)
      | r1_tarski(A_716,B_717) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_7785,plain,(
    ! [A_722,B_723] :
      ( ~ v1_xboole_0(A_722)
      | r1_tarski(A_722,B_723) ) ),
    inference(resolution,[status(thm)],[c_7720,c_2])).

tff(c_7789,plain,(
    ! [A_722,B_723] :
      ( k3_xboole_0(A_722,B_723) = A_722
      | ~ v1_xboole_0(A_722) ) ),
    inference(resolution,[status(thm)],[c_7785,c_16])).

tff(c_9728,plain,(
    ! [B_888,B_889] : k3_xboole_0(k2_zfmisc_1(B_888,'#skF_8'),B_889) = k2_zfmisc_1(B_888,'#skF_8') ),
    inference(resolution,[status(thm)],[c_9122,c_7789])).

tff(c_8049,plain,(
    ! [A_756,B_757] :
      ( r2_hidden('#skF_3'(A_756,B_757),k3_xboole_0(A_756,B_757))
      | r1_xboole_0(A_756,B_757) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8075,plain,(
    ! [A_756,B_757] :
      ( ~ v1_xboole_0(k3_xboole_0(A_756,B_757))
      | r1_xboole_0(A_756,B_757) ) ),
    inference(resolution,[status(thm)],[c_8049,c_2])).

tff(c_9747,plain,(
    ! [B_888,B_889] :
      ( ~ v1_xboole_0(k2_zfmisc_1(B_888,'#skF_8'))
      | r1_xboole_0(k2_zfmisc_1(B_888,'#skF_8'),B_889) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9728,c_8075])).

tff(c_9790,plain,(
    ! [B_890,B_891] : r1_xboole_0(k2_zfmisc_1(B_890,'#skF_8'),B_891) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9118,c_9747])).

tff(c_7740,plain,(
    ! [A_718] : r1_tarski(A_718,A_718) ),
    inference(resolution,[status(thm)],[c_7720,c_8])).

tff(c_7752,plain,(
    ! [A_720] : k3_xboole_0(A_720,A_720) = A_720 ),
    inference(resolution,[status(thm)],[c_7740,c_16])).

tff(c_7758,plain,(
    ! [A_720,C_14] :
      ( ~ r1_xboole_0(A_720,A_720)
      | ~ r2_hidden(C_14,A_720) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7752,c_14])).

tff(c_9927,plain,(
    ! [C_898,B_899] : ~ r2_hidden(C_898,k2_zfmisc_1(B_899,'#skF_8')) ),
    inference(resolution,[status(thm)],[c_9790,c_7758])).

tff(c_9939,plain,(
    ! [B_899,C_728] : v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(B_899,'#skF_8'),C_728)) ),
    inference(resolution,[status(thm)],[c_7803,c_9927])).

tff(c_9983,plain,(
    ! [B_899,C_728] : v1_xboole_0(k3_zfmisc_1(B_899,'#skF_8',C_728)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_9939])).

tff(c_10007,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9983,c_52])).

tff(c_10008,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_5667])).

tff(c_5707,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_5668,c_2])).

tff(c_10209,plain,(
    ! [C_936,B_937,A_938] :
      ( r2_hidden(C_936,B_937)
      | ~ r2_hidden(C_936,A_938)
      | ~ r1_tarski(A_938,B_937) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10225,plain,(
    ! [A_939,B_940] :
      ( r2_hidden('#skF_1'(A_939),B_940)
      | ~ r1_tarski(A_939,B_940)
      | v1_xboole_0(A_939) ) ),
    inference(resolution,[status(thm)],[c_4,c_10209])).

tff(c_10395,plain,(
    ! [B_953,A_954] :
      ( ~ v1_xboole_0(B_953)
      | ~ r1_tarski(A_954,B_953)
      | v1_xboole_0(A_954) ) ),
    inference(resolution,[status(thm)],[c_10225,c_2])).

tff(c_10410,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_5680,c_10395])).

tff(c_10424,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_5707,c_10410])).

tff(c_10390,plain,(
    ! [A_949,B_950,C_951,D_952] :
      ( k7_mcart_1(A_949,B_950,C_951,D_952) = k2_mcart_1(D_952)
      | ~ m1_subset_1(D_952,k3_zfmisc_1(A_949,B_950,C_951))
      | k1_xboole_0 = C_951
      | k1_xboole_0 = B_950
      | k1_xboole_0 = A_949 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_10394,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_10390])).

tff(c_10431,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_10394])).

tff(c_10063,plain,(
    ! [A_912,B_913] :
      ( ~ r2_hidden('#skF_2'(A_912,B_913),B_913)
      | r1_tarski(A_912,B_913) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10084,plain,(
    ! [A_917] : r1_tarski(A_917,A_917) ),
    inference(resolution,[status(thm)],[c_10,c_10063])).

tff(c_10089,plain,(
    ! [A_918] : k3_xboole_0(A_918,A_918) = A_918 ),
    inference(resolution,[status(thm)],[c_10084,c_16])).

tff(c_10014,plain,(
    ! [A_901,B_902,C_903] :
      ( ~ r1_xboole_0(A_901,B_902)
      | ~ r2_hidden(C_903,k3_xboole_0(A_901,B_902)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10028,plain,(
    ! [A_901,B_902] :
      ( ~ r1_xboole_0(A_901,B_902)
      | v1_xboole_0(k3_xboole_0(A_901,B_902)) ) ),
    inference(resolution,[status(thm)],[c_4,c_10014])).

tff(c_10104,plain,(
    ! [A_919] :
      ( ~ r1_xboole_0(A_919,A_919)
      | v1_xboole_0(A_919) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10089,c_10028])).

tff(c_10109,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_10104])).

tff(c_10438,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10431,c_10109])).

tff(c_10441,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10424,c_10438])).

tff(c_10443,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_10394])).

tff(c_10637,plain,(
    ! [A_968,B_969,C_970,D_971] :
      ( k5_mcart_1(A_968,B_969,C_970,D_971) = k1_mcart_1(k1_mcart_1(D_971))
      | ~ m1_subset_1(D_971,k3_zfmisc_1(A_968,B_969,C_970))
      | k1_xboole_0 = C_970
      | k1_xboole_0 = B_969
      | k1_xboole_0 = A_968 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_10640,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_10637])).

tff(c_10643,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_10443,c_10640])).

tff(c_10883,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_10643])).

tff(c_10017,plain,(
    ! [C_903] :
      ( ~ r1_xboole_0('#skF_8','#skF_5')
      | ~ r2_hidden(C_903,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5698,c_10014])).

tff(c_10029,plain,(
    ~ r1_xboole_0('#skF_8','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_10017])).

tff(c_10251,plain,(
    ! [A_941,B_942] :
      ( r2_hidden('#skF_3'(A_941,B_942),k3_xboole_0(A_941,B_942))
      | r1_xboole_0(A_941,B_942) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10268,plain,
    ( r2_hidden('#skF_3'('#skF_8','#skF_5'),'#skF_8')
    | r1_xboole_0('#skF_8','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5698,c_10251])).

tff(c_10279,plain,(
    r2_hidden('#skF_3'('#skF_8','#skF_5'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_10029,c_10268])).

tff(c_10471,plain,(
    ! [B_956] :
      ( r2_hidden('#skF_3'('#skF_8','#skF_5'),B_956)
      | ~ r1_tarski('#skF_8',B_956) ) ),
    inference(resolution,[status(thm)],[c_10279,c_6])).

tff(c_10148,plain,(
    ! [A_924,C_925] :
      ( ~ r1_xboole_0(A_924,A_924)
      | ~ r2_hidden(C_925,A_924) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10089,c_14])).

tff(c_10152,plain,(
    ! [C_925] : ~ r2_hidden(C_925,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_10148])).

tff(c_10493,plain,(
    ~ r1_tarski('#skF_8',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10471,c_10152])).

tff(c_10887,plain,(
    ~ r1_tarski('#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10883,c_10493])).

tff(c_10900,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5681,c_10887])).

tff(c_10902,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_10643])).

tff(c_10497,plain,(
    ! [A_957,B_958,C_959,D_960] :
      ( k6_mcart_1(A_957,B_958,C_959,D_960) = k2_mcart_1(k1_mcart_1(D_960))
      | ~ m1_subset_1(D_960,k3_zfmisc_1(A_957,B_958,C_959))
      | k1_xboole_0 = C_959
      | k1_xboole_0 = B_958
      | k1_xboole_0 = A_957 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_10500,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_10497])).

tff(c_10503,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_10443,c_10500])).

tff(c_11004,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_10902,c_10503])).

tff(c_11005,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_11004])).

tff(c_10020,plain,(
    ! [C_903] :
      ( ~ r1_xboole_0('#skF_9','#skF_6')
      | ~ r2_hidden(C_903,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5699,c_10014])).

tff(c_10030,plain,(
    ~ r1_xboole_0('#skF_9','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_10020])).

tff(c_10271,plain,
    ( r2_hidden('#skF_3'('#skF_9','#skF_6'),'#skF_9')
    | r1_xboole_0('#skF_9','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_5699,c_10251])).

tff(c_10280,plain,(
    r2_hidden('#skF_3'('#skF_9','#skF_6'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_10030,c_10271])).

tff(c_10523,plain,(
    ! [B_962] :
      ( r2_hidden('#skF_3'('#skF_9','#skF_6'),B_962)
      | ~ r1_tarski('#skF_9',B_962) ) ),
    inference(resolution,[status(thm)],[c_10280,c_6])).

tff(c_10545,plain,(
    ~ r1_tarski('#skF_9',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10523,c_10152])).

tff(c_11009,plain,(
    ~ r1_tarski('#skF_9','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11005,c_10545])).

tff(c_11024,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5679,c_11009])).

tff(c_11025,plain,(
    k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') ),
    inference(splitRight,[status(thm)],[c_11004])).

tff(c_10171,plain,(
    ! [A_928,B_929,C_930] :
      ( r2_hidden(k1_mcart_1(A_928),B_929)
      | ~ r2_hidden(A_928,k2_zfmisc_1(B_929,C_930)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_11327,plain,(
    ! [A_1028,A_1029,B_1030,C_1031] :
      ( r2_hidden(k1_mcart_1(A_1028),k2_zfmisc_1(A_1029,B_1030))
      | ~ r2_hidden(A_1028,k3_zfmisc_1(A_1029,B_1030,C_1031)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_10171])).

tff(c_11382,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_38,c_11327])).

tff(c_11498,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')),'#skF_8') ),
    inference(resolution,[status(thm)],[c_11382,c_26])).

tff(c_11506,plain,(
    r2_hidden(k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11025,c_11498])).

tff(c_11508,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10008,c_11506])).

tff(c_11509,plain,(
    ! [C_903] : ~ r2_hidden(C_903,'#skF_9') ),
    inference(splitRight,[status(thm)],[c_10020])).

tff(c_10009,plain,(
    r2_hidden(k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_5667])).

tff(c_11512,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11509,c_10009])).

tff(c_11513,plain,(
    ! [C_903] : ~ r2_hidden(C_903,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_10017])).

tff(c_12627,plain,(
    ! [B_1125] : v1_xboole_0(k2_zfmisc_1(B_1125,'#skF_8')) ),
    inference(resolution,[status(thm)],[c_12592,c_11513])).

tff(c_12631,plain,(
    ! [B_1127] : v1_xboole_0(k2_zfmisc_1(B_1127,'#skF_8')) ),
    inference(resolution,[status(thm)],[c_12592,c_11513])).

tff(c_11538,plain,(
    ! [A_1042,B_1043] :
      ( r2_hidden('#skF_2'(A_1042,B_1043),A_1042)
      | r1_tarski(A_1042,B_1043) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_11624,plain,(
    ! [A_1051,B_1052] :
      ( ~ v1_xboole_0(A_1051)
      | r1_tarski(A_1051,B_1052) ) ),
    inference(resolution,[status(thm)],[c_11538,c_2])).

tff(c_11628,plain,(
    ! [A_1051,B_1052] :
      ( k3_xboole_0(A_1051,B_1052) = A_1051
      | ~ v1_xboole_0(A_1051) ) ),
    inference(resolution,[status(thm)],[c_11624,c_16])).

tff(c_12793,plain,(
    ! [B_1149,B_1150] : k3_xboole_0(k2_zfmisc_1(B_1149,'#skF_8'),B_1150) = k2_zfmisc_1(B_1149,'#skF_8') ),
    inference(resolution,[status(thm)],[c_12631,c_11628])).

tff(c_11860,plain,(
    ! [A_1080,B_1081] :
      ( r2_hidden('#skF_3'(A_1080,B_1081),k3_xboole_0(A_1080,B_1081))
      | r1_xboole_0(A_1080,B_1081) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_11886,plain,(
    ! [A_1080,B_1081] :
      ( ~ v1_xboole_0(k3_xboole_0(A_1080,B_1081))
      | r1_xboole_0(A_1080,B_1081) ) ),
    inference(resolution,[status(thm)],[c_11860,c_2])).

tff(c_12805,plain,(
    ! [B_1149,B_1150] :
      ( ~ v1_xboole_0(k2_zfmisc_1(B_1149,'#skF_8'))
      | r1_xboole_0(k2_zfmisc_1(B_1149,'#skF_8'),B_1150) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12793,c_11886])).

tff(c_12841,plain,(
    ! [B_1151,B_1152] : r1_xboole_0(k2_zfmisc_1(B_1151,'#skF_8'),B_1152) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12627,c_12805])).

tff(c_11558,plain,(
    ! [A_1044] : r1_tarski(A_1044,A_1044) ),
    inference(resolution,[status(thm)],[c_11538,c_8])).

tff(c_11569,plain,(
    ! [A_1046] : k3_xboole_0(A_1046,A_1046) = A_1046 ),
    inference(resolution,[status(thm)],[c_11558,c_16])).

tff(c_11578,plain,(
    ! [A_1046,C_14] :
      ( ~ r1_xboole_0(A_1046,A_1046)
      | ~ r2_hidden(C_14,A_1046) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11569,c_14])).

tff(c_12949,plain,(
    ! [C_1159,B_1160] : ~ r2_hidden(C_1159,k2_zfmisc_1(B_1160,'#skF_8')) ),
    inference(resolution,[status(thm)],[c_12841,c_11578])).

tff(c_12957,plain,(
    ! [B_1160,C_1056] : v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(B_1160,'#skF_8'),C_1056)) ),
    inference(resolution,[status(thm)],[c_11645,c_12949])).

tff(c_13000,plain,(
    ! [B_1160,C_1056] : v1_xboole_0(k3_zfmisc_1(B_1160,'#skF_8',C_1056)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_12957])).

tff(c_13024,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13000,c_52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:22:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.04/2.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.36/2.76  
% 7.36/2.76  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.36/2.77  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_2
% 7.36/2.77  
% 7.36/2.77  %Foreground sorts:
% 7.36/2.77  
% 7.36/2.77  
% 7.36/2.77  %Background operators:
% 7.36/2.77  
% 7.36/2.77  
% 7.36/2.77  %Foreground operators:
% 7.36/2.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.36/2.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.36/2.77  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.36/2.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.36/2.77  tff('#skF_7', type, '#skF_7': $i).
% 7.36/2.77  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.36/2.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.36/2.77  tff('#skF_10', type, '#skF_10': $i).
% 7.36/2.77  tff('#skF_5', type, '#skF_5': $i).
% 7.36/2.77  tff('#skF_6', type, '#skF_6': $i).
% 7.36/2.77  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.36/2.77  tff('#skF_9', type, '#skF_9': $i).
% 7.36/2.77  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 7.36/2.77  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 7.36/2.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.36/2.77  tff('#skF_8', type, '#skF_8': $i).
% 7.36/2.77  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 7.36/2.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.36/2.77  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 7.36/2.77  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.36/2.77  tff('#skF_4', type, '#skF_4': $i).
% 7.36/2.77  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 7.36/2.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.36/2.77  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.36/2.77  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 7.36/2.77  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.36/2.77  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.36/2.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.36/2.77  
% 7.36/2.80  tff(f_64, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 7.36/2.80  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.36/2.80  tff(f_70, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 7.36/2.80  tff(f_110, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (![F]: (m1_subset_1(F, k1_zfmisc_1(C)) => (![G]: (m1_subset_1(G, k3_zfmisc_1(A, B, C)) => (r2_hidden(G, k3_zfmisc_1(D, E, F)) => ((r2_hidden(k5_mcart_1(A, B, C, G), D) & r2_hidden(k6_mcart_1(A, B, C, G), E)) & r2_hidden(k7_mcart_1(A, B, C, G), F))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_mcart_1)).
% 7.36/2.80  tff(f_62, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.36/2.80  tff(f_90, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 7.36/2.80  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.36/2.80  tff(f_58, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 7.36/2.80  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.36/2.80  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 7.36/2.80  tff(c_24, plain, (![A_20, B_21, C_22]: (k2_zfmisc_1(k2_zfmisc_1(A_20, B_21), C_22)=k3_zfmisc_1(A_20, B_21, C_22))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.36/2.80  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.36/2.80  tff(c_11635, plain, (![A_1054, B_1055, C_1056]: (r2_hidden(k1_mcart_1(A_1054), B_1055) | ~r2_hidden(A_1054, k2_zfmisc_1(B_1055, C_1056)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.36/2.80  tff(c_11645, plain, (![B_1055, C_1056]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_1055, C_1056))), B_1055) | v1_xboole_0(k2_zfmisc_1(B_1055, C_1056)))), inference(resolution, [status(thm)], [c_4, c_11635])).
% 7.36/2.80  tff(c_11760, plain, (![A_1073, C_1074, B_1075]: (r2_hidden(k2_mcart_1(A_1073), C_1074) | ~r2_hidden(A_1073, k2_zfmisc_1(B_1075, C_1074)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.36/2.80  tff(c_12592, plain, (![B_1125, C_1126]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_1125, C_1126))), C_1126) | v1_xboole_0(k2_zfmisc_1(B_1125, C_1126)))), inference(resolution, [status(thm)], [c_4, c_11760])).
% 7.36/2.80  tff(c_7795, plain, (![A_726, B_727, C_728]: (r2_hidden(k1_mcart_1(A_726), B_727) | ~r2_hidden(A_726, k2_zfmisc_1(B_727, C_728)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.36/2.80  tff(c_7803, plain, (![B_727, C_728]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_727, C_728))), B_727) | v1_xboole_0(k2_zfmisc_1(B_727, C_728)))), inference(resolution, [status(thm)], [c_4, c_7795])).
% 7.36/2.80  tff(c_7810, plain, (![A_731, C_732, B_733]: (r2_hidden(k2_mcart_1(A_731), C_732) | ~r2_hidden(A_731, k2_zfmisc_1(B_733, C_732)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.36/2.80  tff(c_9083, plain, (![B_824, C_825]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_824, C_825))), C_825) | v1_xboole_0(k2_zfmisc_1(B_824, C_825)))), inference(resolution, [status(thm)], [c_4, c_7810])).
% 7.36/2.80  tff(c_42, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.36/2.80  tff(c_5669, plain, (![A_536, B_537]: (r1_tarski(A_536, B_537) | ~m1_subset_1(A_536, k1_zfmisc_1(B_537)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.36/2.80  tff(c_5679, plain, (r1_tarski('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_42, c_5669])).
% 7.36/2.80  tff(c_44, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.36/2.80  tff(c_5681, plain, (r1_tarski('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_5669])).
% 7.36/2.80  tff(c_38, plain, (r2_hidden('#skF_10', k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.36/2.80  tff(c_5913, plain, (![A_577, C_578, B_579]: (r2_hidden(k2_mcart_1(A_577), C_578) | ~r2_hidden(A_577, k2_zfmisc_1(B_579, C_578)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.36/2.80  tff(c_6499, plain, (![A_623, C_624, A_625, B_626]: (r2_hidden(k2_mcart_1(A_623), C_624) | ~r2_hidden(A_623, k3_zfmisc_1(A_625, B_626, C_624)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_5913])).
% 7.36/2.80  tff(c_6534, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_38, c_6499])).
% 7.36/2.80  tff(c_46, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.36/2.80  tff(c_5680, plain, (r1_tarski('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_5669])).
% 7.36/2.80  tff(c_40, plain, (m1_subset_1('#skF_10', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.36/2.80  tff(c_6146, plain, (![A_594, B_595, C_596, D_597]: (k7_mcart_1(A_594, B_595, C_596, D_597)=k2_mcart_1(D_597) | ~m1_subset_1(D_597, k3_zfmisc_1(A_594, B_595, C_596)) | k1_xboole_0=C_596 | k1_xboole_0=B_595 | k1_xboole_0=A_594)), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.36/2.80  tff(c_6150, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_40, c_6146])).
% 7.36/2.80  tff(c_6211, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_6150])).
% 7.36/2.80  tff(c_3517, plain, (![A_348, B_349, C_350]: (r2_hidden(k1_mcart_1(A_348), B_349) | ~r2_hidden(A_348, k2_zfmisc_1(B_349, C_350)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.36/2.80  tff(c_3525, plain, (![B_349, C_350]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_349, C_350))), B_349) | v1_xboole_0(k2_zfmisc_1(B_349, C_350)))), inference(resolution, [status(thm)], [c_4, c_3517])).
% 7.36/2.80  tff(c_4574, plain, (![B_441, C_442]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_441, C_442))), B_441) | v1_xboole_0(k2_zfmisc_1(B_441, C_442)))), inference(resolution, [status(thm)], [c_4, c_3517])).
% 7.36/2.80  tff(c_36, plain, (~r2_hidden(k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_9') | ~r2_hidden(k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_8') | ~r2_hidden(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.36/2.80  tff(c_58, plain, (~r2_hidden(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_7')), inference(splitLeft, [status(thm)], [c_36])).
% 7.36/2.80  tff(c_59, plain, (![A_46, B_47]: (r1_tarski(A_46, B_47) | ~m1_subset_1(A_46, k1_zfmisc_1(B_47)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.36/2.80  tff(c_69, plain, (r1_tarski('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_42, c_59])).
% 7.36/2.80  tff(c_71, plain, (r1_tarski('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_59])).
% 7.36/2.80  tff(c_70, plain, (r1_tarski('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_59])).
% 7.36/2.80  tff(c_295, plain, (![C_87, B_88, A_89]: (r2_hidden(C_87, B_88) | ~r2_hidden(C_87, A_89) | ~r1_tarski(A_89, B_88))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.36/2.80  tff(c_305, plain, (![A_90, B_91]: (r2_hidden('#skF_1'(A_90), B_91) | ~r1_tarski(A_90, B_91) | v1_xboole_0(A_90))), inference(resolution, [status(thm)], [c_4, c_295])).
% 7.36/2.80  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.36/2.80  tff(c_366, plain, (![B_94, A_95]: (~v1_xboole_0(B_94) | ~r1_tarski(A_95, B_94) | v1_xboole_0(A_95))), inference(resolution, [status(thm)], [c_305, c_2])).
% 7.36/2.80  tff(c_394, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_70, c_366])).
% 7.36/2.80  tff(c_397, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_394])).
% 7.36/2.80  tff(c_467, plain, (![A_99, B_100, C_101, D_102]: (k7_mcart_1(A_99, B_100, C_101, D_102)=k2_mcart_1(D_102) | ~m1_subset_1(D_102, k3_zfmisc_1(A_99, B_100, C_101)) | k1_xboole_0=C_101 | k1_xboole_0=B_100 | k1_xboole_0=A_99)), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.36/2.80  tff(c_471, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_40, c_467])).
% 7.36/2.80  tff(c_535, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_471])).
% 7.36/2.80  tff(c_18, plain, (![A_17]: (r1_xboole_0(A_17, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.36/2.80  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.36/2.80  tff(c_113, plain, (![A_58, B_59]: (~r2_hidden('#skF_2'(A_58, B_59), B_59) | r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.36/2.80  tff(c_119, plain, (![A_60]: (r1_tarski(A_60, A_60))), inference(resolution, [status(thm)], [c_10, c_113])).
% 7.36/2.80  tff(c_16, plain, (![A_15, B_16]: (k3_xboole_0(A_15, B_16)=A_15 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.36/2.80  tff(c_144, plain, (![A_64]: (k3_xboole_0(A_64, A_64)=A_64)), inference(resolution, [status(thm)], [c_119, c_16])).
% 7.36/2.80  tff(c_14, plain, (![A_10, B_11, C_14]: (~r1_xboole_0(A_10, B_11) | ~r2_hidden(C_14, k3_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.36/2.80  tff(c_159, plain, (![A_65, C_66]: (~r1_xboole_0(A_65, A_65) | ~r2_hidden(C_66, A_65))), inference(superposition, [status(thm), theory('equality')], [c_144, c_14])).
% 7.36/2.80  tff(c_164, plain, (![C_67]: (~r2_hidden(C_67, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_159])).
% 7.36/2.80  tff(c_174, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_164])).
% 7.36/2.80  tff(c_541, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_535, c_174])).
% 7.36/2.80  tff(c_545, plain, $false, inference(negUnitSimplification, [status(thm)], [c_397, c_541])).
% 7.36/2.80  tff(c_547, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_471])).
% 7.36/2.80  tff(c_719, plain, (![A_119, B_120, C_121, D_122]: (k6_mcart_1(A_119, B_120, C_121, D_122)=k2_mcart_1(k1_mcart_1(D_122)) | ~m1_subset_1(D_122, k3_zfmisc_1(A_119, B_120, C_121)) | k1_xboole_0=C_121 | k1_xboole_0=B_120 | k1_xboole_0=A_119)), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.36/2.80  tff(c_722, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_40, c_719])).
% 7.36/2.80  tff(c_725, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_547, c_722])).
% 7.36/2.80  tff(c_780, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_725])).
% 7.36/2.80  tff(c_72, plain, (![A_48, B_49]: (k3_xboole_0(A_48, B_49)=A_48 | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.36/2.80  tff(c_82, plain, (k3_xboole_0('#skF_8', '#skF_5')='#skF_8'), inference(resolution, [status(thm)], [c_71, c_72])).
% 7.36/2.80  tff(c_124, plain, (![A_61, B_62, C_63]: (~r1_xboole_0(A_61, B_62) | ~r2_hidden(C_63, k3_xboole_0(A_61, B_62)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.36/2.80  tff(c_137, plain, (![C_63]: (~r1_xboole_0('#skF_8', '#skF_5') | ~r2_hidden(C_63, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_124])).
% 7.36/2.80  tff(c_158, plain, (~r1_xboole_0('#skF_8', '#skF_5')), inference(splitLeft, [status(thm)], [c_137])).
% 7.36/2.80  tff(c_398, plain, (![A_96, B_97]: (r2_hidden('#skF_3'(A_96, B_97), k3_xboole_0(A_96, B_97)) | r1_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.36/2.80  tff(c_421, plain, (r2_hidden('#skF_3'('#skF_8', '#skF_5'), '#skF_8') | r1_xboole_0('#skF_8', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_82, c_398])).
% 7.36/2.80  tff(c_428, plain, (r2_hidden('#skF_3'('#skF_8', '#skF_5'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_158, c_421])).
% 7.36/2.80  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.36/2.80  tff(c_600, plain, (![B_113]: (r2_hidden('#skF_3'('#skF_8', '#skF_5'), B_113) | ~r1_tarski('#skF_8', B_113))), inference(resolution, [status(thm)], [c_428, c_6])).
% 7.36/2.80  tff(c_163, plain, (![C_66]: (~r2_hidden(C_66, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_159])).
% 7.36/2.80  tff(c_623, plain, (~r1_tarski('#skF_8', k1_xboole_0)), inference(resolution, [status(thm)], [c_600, c_163])).
% 7.36/2.80  tff(c_783, plain, (~r1_tarski('#skF_8', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_780, c_623])).
% 7.36/2.80  tff(c_797, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_783])).
% 7.36/2.80  tff(c_799, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_725])).
% 7.36/2.80  tff(c_593, plain, (![A_109, B_110, C_111, D_112]: (k5_mcart_1(A_109, B_110, C_111, D_112)=k1_mcart_1(k1_mcart_1(D_112)) | ~m1_subset_1(D_112, k3_zfmisc_1(A_109, B_110, C_111)) | k1_xboole_0=C_111 | k1_xboole_0=B_110 | k1_xboole_0=A_109)), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.36/2.80  tff(c_596, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_40, c_593])).
% 7.36/2.80  tff(c_599, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_547, c_596])).
% 7.36/2.80  tff(c_913, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_799, c_599])).
% 7.36/2.80  tff(c_914, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_913])).
% 7.36/2.80  tff(c_84, plain, (k3_xboole_0('#skF_9', '#skF_6')='#skF_9'), inference(resolution, [status(thm)], [c_69, c_72])).
% 7.36/2.80  tff(c_131, plain, (![C_63]: (~r1_xboole_0('#skF_9', '#skF_6') | ~r2_hidden(C_63, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_84, c_124])).
% 7.36/2.80  tff(c_156, plain, (~r1_xboole_0('#skF_9', '#skF_6')), inference(splitLeft, [status(thm)], [c_131])).
% 7.36/2.80  tff(c_415, plain, (r2_hidden('#skF_3'('#skF_9', '#skF_6'), '#skF_9') | r1_xboole_0('#skF_9', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_84, c_398])).
% 7.36/2.80  tff(c_426, plain, (r2_hidden('#skF_3'('#skF_9', '#skF_6'), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_156, c_415])).
% 7.36/2.80  tff(c_650, plain, (![B_115]: (r2_hidden('#skF_3'('#skF_9', '#skF_6'), B_115) | ~r1_tarski('#skF_9', B_115))), inference(resolution, [status(thm)], [c_426, c_6])).
% 7.36/2.80  tff(c_673, plain, (~r1_tarski('#skF_9', k1_xboole_0)), inference(resolution, [status(thm)], [c_650, c_163])).
% 7.36/2.80  tff(c_917, plain, (~r1_tarski('#skF_9', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_914, c_673])).
% 7.36/2.80  tff(c_932, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69, c_917])).
% 7.36/2.80  tff(c_933, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')), inference(splitRight, [status(thm)], [c_913])).
% 7.36/2.80  tff(c_212, plain, (![A_73, B_74, C_75]: (k2_zfmisc_1(k2_zfmisc_1(A_73, B_74), C_75)=k3_zfmisc_1(A_73, B_74, C_75))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.36/2.80  tff(c_28, plain, (![A_23, B_24, C_25]: (r2_hidden(k1_mcart_1(A_23), B_24) | ~r2_hidden(A_23, k2_zfmisc_1(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.36/2.80  tff(c_1682, plain, (![A_202, A_203, B_204, C_205]: (r2_hidden(k1_mcart_1(A_202), k2_zfmisc_1(A_203, B_204)) | ~r2_hidden(A_202, k3_zfmisc_1(A_203, B_204, C_205)))), inference(superposition, [status(thm), theory('equality')], [c_212, c_28])).
% 7.36/2.80  tff(c_1732, plain, (r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_38, c_1682])).
% 7.36/2.80  tff(c_1738, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')), '#skF_7')), inference(resolution, [status(thm)], [c_1732, c_28])).
% 7.36/2.80  tff(c_1746, plain, (r2_hidden(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_933, c_1738])).
% 7.36/2.80  tff(c_1748, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1746])).
% 7.36/2.80  tff(c_1749, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_394])).
% 7.36/2.80  tff(c_102, plain, (![A_52, B_53]: (r2_hidden('#skF_2'(A_52, B_53), A_52) | r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.36/2.80  tff(c_107, plain, (![A_54, B_55]: (~v1_xboole_0(A_54) | r1_tarski(A_54, B_55))), inference(resolution, [status(thm)], [c_102, c_2])).
% 7.36/2.80  tff(c_111, plain, (![A_54, B_55]: (k3_xboole_0(A_54, B_55)=A_54 | ~v1_xboole_0(A_54))), inference(resolution, [status(thm)], [c_107, c_16])).
% 7.36/2.80  tff(c_1753, plain, (![B_55]: (k3_xboole_0('#skF_7', B_55)='#skF_7')), inference(resolution, [status(thm)], [c_1749, c_111])).
% 7.36/2.80  tff(c_1821, plain, (![A_209, B_210]: (r2_hidden('#skF_3'(A_209, B_210), k3_xboole_0(A_209, B_210)) | r1_xboole_0(A_209, B_210))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.36/2.80  tff(c_2060, plain, (![A_226, B_227]: (~v1_xboole_0(k3_xboole_0(A_226, B_227)) | r1_xboole_0(A_226, B_227))), inference(resolution, [status(thm)], [c_1821, c_2])).
% 7.36/2.80  tff(c_2063, plain, (![B_55]: (~v1_xboole_0('#skF_7') | r1_xboole_0('#skF_7', B_55))), inference(superposition, [status(thm), theory('equality')], [c_1753, c_2060])).
% 7.36/2.80  tff(c_2083, plain, (![B_55]: (r1_xboole_0('#skF_7', B_55))), inference(demodulation, [status(thm), theory('equality')], [c_1749, c_2063])).
% 7.36/2.80  tff(c_83, plain, (k3_xboole_0('#skF_7', '#skF_4')='#skF_7'), inference(resolution, [status(thm)], [c_70, c_72])).
% 7.36/2.80  tff(c_134, plain, (![C_63]: (~r1_xboole_0('#skF_7', '#skF_4') | ~r2_hidden(C_63, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_83, c_124])).
% 7.36/2.80  tff(c_157, plain, (~r1_xboole_0('#skF_7', '#skF_4')), inference(splitLeft, [status(thm)], [c_134])).
% 7.36/2.80  tff(c_2093, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2083, c_157])).
% 7.36/2.80  tff(c_2094, plain, (![C_63]: (~r2_hidden(C_63, '#skF_8'))), inference(splitRight, [status(thm)], [c_137])).
% 7.36/2.80  tff(c_2252, plain, (![A_248, B_249, C_250]: (k2_zfmisc_1(k2_zfmisc_1(A_248, B_249), C_250)=k3_zfmisc_1(A_248, B_249, C_250))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.36/2.80  tff(c_3411, plain, (![A_341, A_342, B_343, C_344]: (r2_hidden(k1_mcart_1(A_341), k2_zfmisc_1(A_342, B_343)) | ~r2_hidden(A_341, k3_zfmisc_1(A_342, B_343, C_344)))), inference(superposition, [status(thm), theory('equality')], [c_2252, c_28])).
% 7.36/2.80  tff(c_3458, plain, (r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_38, c_3411])).
% 7.36/2.80  tff(c_26, plain, (![A_23, C_25, B_24]: (r2_hidden(k2_mcart_1(A_23), C_25) | ~r2_hidden(A_23, k2_zfmisc_1(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.36/2.80  tff(c_3460, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')), '#skF_8')), inference(resolution, [status(thm)], [c_3458, c_26])).
% 7.36/2.80  tff(c_3471, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2094, c_3460])).
% 7.36/2.80  tff(c_3472, plain, (![C_63]: (~r2_hidden(C_63, '#skF_7'))), inference(splitRight, [status(thm)], [c_134])).
% 7.36/2.80  tff(c_4611, plain, (![C_442]: (v1_xboole_0(k2_zfmisc_1('#skF_7', C_442)))), inference(resolution, [status(thm)], [c_4574, c_3472])).
% 7.36/2.80  tff(c_4615, plain, (![C_443]: (v1_xboole_0(k2_zfmisc_1('#skF_7', C_443)))), inference(resolution, [status(thm)], [c_4574, c_3472])).
% 7.36/2.80  tff(c_4691, plain, (![C_451, B_452]: (k3_xboole_0(k2_zfmisc_1('#skF_7', C_451), B_452)=k2_zfmisc_1('#skF_7', C_451))), inference(resolution, [status(thm)], [c_4615, c_111])).
% 7.36/2.80  tff(c_3798, plain, (![A_380, B_381]: (r2_hidden('#skF_3'(A_380, B_381), k3_xboole_0(A_380, B_381)) | r1_xboole_0(A_380, B_381))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.36/2.80  tff(c_3824, plain, (![A_380, B_381]: (~v1_xboole_0(k3_xboole_0(A_380, B_381)) | r1_xboole_0(A_380, B_381))), inference(resolution, [status(thm)], [c_3798, c_2])).
% 7.36/2.80  tff(c_4706, plain, (![C_451, B_452]: (~v1_xboole_0(k2_zfmisc_1('#skF_7', C_451)) | r1_xboole_0(k2_zfmisc_1('#skF_7', C_451), B_452))), inference(superposition, [status(thm), theory('equality')], [c_4691, c_3824])).
% 7.36/2.80  tff(c_4777, plain, (![C_456, B_457]: (r1_xboole_0(k2_zfmisc_1('#skF_7', C_456), B_457))), inference(demodulation, [status(thm), theory('equality')], [c_4611, c_4706])).
% 7.36/2.80  tff(c_150, plain, (![A_64, C_14]: (~r1_xboole_0(A_64, A_64) | ~r2_hidden(C_14, A_64))), inference(superposition, [status(thm), theory('equality')], [c_144, c_14])).
% 7.36/2.80  tff(c_4850, plain, (![C_463, C_464]: (~r2_hidden(C_463, k2_zfmisc_1('#skF_7', C_464)))), inference(resolution, [status(thm)], [c_4777, c_150])).
% 7.36/2.80  tff(c_4862, plain, (![C_464, C_350]: (v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1('#skF_7', C_464), C_350)))), inference(resolution, [status(thm)], [c_3525, c_4850])).
% 7.36/2.80  tff(c_4898, plain, (![C_464, C_350]: (v1_xboole_0(k3_zfmisc_1('#skF_7', C_464, C_350)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_4862])).
% 7.36/2.80  tff(c_52, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_38, c_2])).
% 7.36/2.80  tff(c_4922, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4898, c_52])).
% 7.36/2.80  tff(c_4923, plain, (![C_63]: (~r2_hidden(C_63, '#skF_9'))), inference(splitRight, [status(thm)], [c_131])).
% 7.36/2.80  tff(c_5090, plain, (![A_487, C_488, B_489]: (r2_hidden(k2_mcart_1(A_487), C_488) | ~r2_hidden(A_487, k2_zfmisc_1(B_489, C_488)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.36/2.80  tff(c_5636, plain, (![A_532, C_533, A_534, B_535]: (r2_hidden(k2_mcart_1(A_532), C_533) | ~r2_hidden(A_532, k3_zfmisc_1(A_534, B_535, C_533)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_5090])).
% 7.36/2.80  tff(c_5656, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_38, c_5636])).
% 7.36/2.80  tff(c_5666, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4923, c_5656])).
% 7.36/2.80  tff(c_5668, plain, (r2_hidden(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_7')), inference(splitRight, [status(thm)], [c_36])).
% 7.36/2.80  tff(c_5900, plain, (![C_574, B_575, A_576]: (r2_hidden(C_574, B_575) | ~r2_hidden(C_574, A_576) | ~r1_tarski(A_576, B_575))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.36/2.80  tff(c_5936, plain, (![B_581]: (r2_hidden(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), B_581) | ~r1_tarski('#skF_7', B_581))), inference(resolution, [status(thm)], [c_5668, c_5900])).
% 7.36/2.80  tff(c_5734, plain, (![A_547, B_548]: (r2_hidden('#skF_2'(A_547, B_548), A_547) | r1_tarski(A_547, B_548))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.36/2.80  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.36/2.80  tff(c_5749, plain, (![A_549]: (r1_tarski(A_549, A_549))), inference(resolution, [status(thm)], [c_5734, c_8])).
% 7.36/2.80  tff(c_5754, plain, (![A_550]: (k3_xboole_0(A_550, A_550)=A_550)), inference(resolution, [status(thm)], [c_5749, c_16])).
% 7.36/2.80  tff(c_5773, plain, (![A_555, C_556]: (~r1_xboole_0(A_555, A_555) | ~r2_hidden(C_556, A_555))), inference(superposition, [status(thm), theory('equality')], [c_5754, c_14])).
% 7.36/2.80  tff(c_5777, plain, (![C_556]: (~r2_hidden(C_556, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_5773])).
% 7.36/2.80  tff(c_5959, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_5936, c_5777])).
% 7.36/2.80  tff(c_6214, plain, (~r1_tarski('#skF_7', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6211, c_5959])).
% 7.36/2.80  tff(c_6222, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5680, c_6214])).
% 7.36/2.80  tff(c_6223, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_6' | k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitRight, [status(thm)], [c_6150])).
% 7.36/2.80  tff(c_6867, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitLeft, [status(thm)], [c_6223])).
% 7.36/2.80  tff(c_5667, plain, (~r2_hidden(k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_8') | ~r2_hidden(k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_9')), inference(splitRight, [status(thm)], [c_36])).
% 7.36/2.80  tff(c_5716, plain, (~r2_hidden(k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_9')), inference(splitLeft, [status(thm)], [c_5667])).
% 7.36/2.80  tff(c_6922, plain, (~r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_6867, c_5716])).
% 7.36/2.80  tff(c_6925, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6534, c_6922])).
% 7.36/2.80  tff(c_6926, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_6223])).
% 7.36/2.80  tff(c_6928, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_6926])).
% 7.36/2.80  tff(c_5687, plain, (![A_540, B_541]: (k3_xboole_0(A_540, B_541)=A_540 | ~r1_tarski(A_540, B_541))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.36/2.80  tff(c_5698, plain, (k3_xboole_0('#skF_8', '#skF_5')='#skF_8'), inference(resolution, [status(thm)], [c_5681, c_5687])).
% 7.36/2.80  tff(c_5718, plain, (![A_544, B_545, C_546]: (~r1_xboole_0(A_544, B_545) | ~r2_hidden(C_546, k3_xboole_0(A_544, B_545)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.36/2.80  tff(c_5721, plain, (![C_546]: (~r1_xboole_0('#skF_8', '#skF_5') | ~r2_hidden(C_546, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_5698, c_5718])).
% 7.36/2.80  tff(c_5733, plain, (~r1_xboole_0('#skF_8', '#skF_5')), inference(splitLeft, [status(thm)], [c_5721])).
% 7.36/2.80  tff(c_6009, plain, (![A_586, B_587]: (r2_hidden('#skF_3'(A_586, B_587), k3_xboole_0(A_586, B_587)) | r1_xboole_0(A_586, B_587))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.36/2.80  tff(c_6026, plain, (r2_hidden('#skF_3'('#skF_8', '#skF_5'), '#skF_8') | r1_xboole_0('#skF_8', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5698, c_6009])).
% 7.36/2.80  tff(c_6037, plain, (r2_hidden('#skF_3'('#skF_8', '#skF_5'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_5733, c_6026])).
% 7.36/2.80  tff(c_6277, plain, (![B_606]: (r2_hidden('#skF_3'('#skF_8', '#skF_5'), B_606) | ~r1_tarski('#skF_8', B_606))), inference(resolution, [status(thm)], [c_6037, c_6])).
% 7.36/2.80  tff(c_6300, plain, (~r1_tarski('#skF_8', k1_xboole_0)), inference(resolution, [status(thm)], [c_6277, c_5777])).
% 7.36/2.80  tff(c_6940, plain, (~r1_tarski('#skF_8', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6928, c_6300])).
% 7.36/2.80  tff(c_6954, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5681, c_6940])).
% 7.36/2.80  tff(c_6956, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_6926])).
% 7.36/2.80  tff(c_6224, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_6150])).
% 7.36/2.80  tff(c_6270, plain, (![A_602, B_603, C_604, D_605]: (k5_mcart_1(A_602, B_603, C_604, D_605)=k1_mcart_1(k1_mcart_1(D_605)) | ~m1_subset_1(D_605, k3_zfmisc_1(A_602, B_603, C_604)) | k1_xboole_0=C_604 | k1_xboole_0=B_603 | k1_xboole_0=A_602)), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.36/2.80  tff(c_6273, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_40, c_6270])).
% 7.36/2.80  tff(c_6276, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_6224, c_6273])).
% 7.36/2.80  tff(c_6957, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_6956, c_6276])).
% 7.36/2.80  tff(c_6958, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_6957])).
% 7.36/2.80  tff(c_5699, plain, (k3_xboole_0('#skF_9', '#skF_6')='#skF_9'), inference(resolution, [status(thm)], [c_5679, c_5687])).
% 7.36/2.80  tff(c_5724, plain, (![C_546]: (~r1_xboole_0('#skF_9', '#skF_6') | ~r2_hidden(C_546, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_5699, c_5718])).
% 7.36/2.80  tff(c_5827, plain, (~r1_xboole_0('#skF_9', '#skF_6')), inference(splitLeft, [status(thm)], [c_5724])).
% 7.36/2.80  tff(c_6029, plain, (r2_hidden('#skF_3'('#skF_9', '#skF_6'), '#skF_9') | r1_xboole_0('#skF_9', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_5699, c_6009])).
% 7.36/2.80  tff(c_6038, plain, (r2_hidden('#skF_3'('#skF_9', '#skF_6'), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_5827, c_6029])).
% 7.36/2.80  tff(c_6225, plain, (![B_600]: (r2_hidden('#skF_3'('#skF_9', '#skF_6'), B_600) | ~r1_tarski('#skF_9', B_600))), inference(resolution, [status(thm)], [c_6038, c_6])).
% 7.36/2.80  tff(c_6248, plain, (~r1_tarski('#skF_9', k1_xboole_0)), inference(resolution, [status(thm)], [c_6225, c_5777])).
% 7.36/2.80  tff(c_6973, plain, (~r1_tarski('#skF_9', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6958, c_6248])).
% 7.36/2.80  tff(c_6985, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5679, c_6973])).
% 7.36/2.80  tff(c_6987, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_6957])).
% 7.36/2.80  tff(c_6955, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_6926])).
% 7.36/2.80  tff(c_6988, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6987, c_6955])).
% 7.36/2.80  tff(c_6989, plain, (![C_546]: (~r2_hidden(C_546, '#skF_9'))), inference(splitRight, [status(thm)], [c_5724])).
% 7.36/2.80  tff(c_7124, plain, (![A_675, B_676, C_677]: (k2_zfmisc_1(k2_zfmisc_1(A_675, B_676), C_677)=k3_zfmisc_1(A_675, B_676, C_677))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.36/2.80  tff(c_7677, plain, (![A_711, C_712, A_713, B_714]: (r2_hidden(k2_mcart_1(A_711), C_712) | ~r2_hidden(A_711, k3_zfmisc_1(A_713, B_714, C_712)))), inference(superposition, [status(thm), theory('equality')], [c_7124, c_26])).
% 7.36/2.80  tff(c_7700, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_38, c_7677])).
% 7.36/2.80  tff(c_7711, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6989, c_7700])).
% 7.36/2.80  tff(c_7712, plain, (![C_546]: (~r2_hidden(C_546, '#skF_8'))), inference(splitRight, [status(thm)], [c_5721])).
% 7.36/2.80  tff(c_9118, plain, (![B_824]: (v1_xboole_0(k2_zfmisc_1(B_824, '#skF_8')))), inference(resolution, [status(thm)], [c_9083, c_7712])).
% 7.36/2.80  tff(c_9122, plain, (![B_826]: (v1_xboole_0(k2_zfmisc_1(B_826, '#skF_8')))), inference(resolution, [status(thm)], [c_9083, c_7712])).
% 7.36/2.80  tff(c_7720, plain, (![A_716, B_717]: (r2_hidden('#skF_2'(A_716, B_717), A_716) | r1_tarski(A_716, B_717))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.36/2.80  tff(c_7785, plain, (![A_722, B_723]: (~v1_xboole_0(A_722) | r1_tarski(A_722, B_723))), inference(resolution, [status(thm)], [c_7720, c_2])).
% 7.36/2.80  tff(c_7789, plain, (![A_722, B_723]: (k3_xboole_0(A_722, B_723)=A_722 | ~v1_xboole_0(A_722))), inference(resolution, [status(thm)], [c_7785, c_16])).
% 7.36/2.80  tff(c_9728, plain, (![B_888, B_889]: (k3_xboole_0(k2_zfmisc_1(B_888, '#skF_8'), B_889)=k2_zfmisc_1(B_888, '#skF_8'))), inference(resolution, [status(thm)], [c_9122, c_7789])).
% 7.36/2.80  tff(c_8049, plain, (![A_756, B_757]: (r2_hidden('#skF_3'(A_756, B_757), k3_xboole_0(A_756, B_757)) | r1_xboole_0(A_756, B_757))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.36/2.80  tff(c_8075, plain, (![A_756, B_757]: (~v1_xboole_0(k3_xboole_0(A_756, B_757)) | r1_xboole_0(A_756, B_757))), inference(resolution, [status(thm)], [c_8049, c_2])).
% 7.36/2.80  tff(c_9747, plain, (![B_888, B_889]: (~v1_xboole_0(k2_zfmisc_1(B_888, '#skF_8')) | r1_xboole_0(k2_zfmisc_1(B_888, '#skF_8'), B_889))), inference(superposition, [status(thm), theory('equality')], [c_9728, c_8075])).
% 7.36/2.80  tff(c_9790, plain, (![B_890, B_891]: (r1_xboole_0(k2_zfmisc_1(B_890, '#skF_8'), B_891))), inference(demodulation, [status(thm), theory('equality')], [c_9118, c_9747])).
% 7.36/2.80  tff(c_7740, plain, (![A_718]: (r1_tarski(A_718, A_718))), inference(resolution, [status(thm)], [c_7720, c_8])).
% 7.36/2.80  tff(c_7752, plain, (![A_720]: (k3_xboole_0(A_720, A_720)=A_720)), inference(resolution, [status(thm)], [c_7740, c_16])).
% 7.36/2.80  tff(c_7758, plain, (![A_720, C_14]: (~r1_xboole_0(A_720, A_720) | ~r2_hidden(C_14, A_720))), inference(superposition, [status(thm), theory('equality')], [c_7752, c_14])).
% 7.36/2.80  tff(c_9927, plain, (![C_898, B_899]: (~r2_hidden(C_898, k2_zfmisc_1(B_899, '#skF_8')))), inference(resolution, [status(thm)], [c_9790, c_7758])).
% 7.36/2.80  tff(c_9939, plain, (![B_899, C_728]: (v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(B_899, '#skF_8'), C_728)))), inference(resolution, [status(thm)], [c_7803, c_9927])).
% 7.36/2.80  tff(c_9983, plain, (![B_899, C_728]: (v1_xboole_0(k3_zfmisc_1(B_899, '#skF_8', C_728)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_9939])).
% 7.36/2.80  tff(c_10007, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9983, c_52])).
% 7.36/2.80  tff(c_10008, plain, (~r2_hidden(k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_8')), inference(splitRight, [status(thm)], [c_5667])).
% 7.36/2.80  tff(c_5707, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_5668, c_2])).
% 7.36/2.80  tff(c_10209, plain, (![C_936, B_937, A_938]: (r2_hidden(C_936, B_937) | ~r2_hidden(C_936, A_938) | ~r1_tarski(A_938, B_937))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.36/2.80  tff(c_10225, plain, (![A_939, B_940]: (r2_hidden('#skF_1'(A_939), B_940) | ~r1_tarski(A_939, B_940) | v1_xboole_0(A_939))), inference(resolution, [status(thm)], [c_4, c_10209])).
% 7.36/2.80  tff(c_10395, plain, (![B_953, A_954]: (~v1_xboole_0(B_953) | ~r1_tarski(A_954, B_953) | v1_xboole_0(A_954))), inference(resolution, [status(thm)], [c_10225, c_2])).
% 7.36/2.80  tff(c_10410, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_5680, c_10395])).
% 7.36/2.80  tff(c_10424, plain, (~v1_xboole_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_5707, c_10410])).
% 7.36/2.80  tff(c_10390, plain, (![A_949, B_950, C_951, D_952]: (k7_mcart_1(A_949, B_950, C_951, D_952)=k2_mcart_1(D_952) | ~m1_subset_1(D_952, k3_zfmisc_1(A_949, B_950, C_951)) | k1_xboole_0=C_951 | k1_xboole_0=B_950 | k1_xboole_0=A_949)), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.36/2.80  tff(c_10394, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_40, c_10390])).
% 7.36/2.80  tff(c_10431, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_10394])).
% 7.36/2.80  tff(c_10063, plain, (![A_912, B_913]: (~r2_hidden('#skF_2'(A_912, B_913), B_913) | r1_tarski(A_912, B_913))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.36/2.80  tff(c_10084, plain, (![A_917]: (r1_tarski(A_917, A_917))), inference(resolution, [status(thm)], [c_10, c_10063])).
% 7.36/2.80  tff(c_10089, plain, (![A_918]: (k3_xboole_0(A_918, A_918)=A_918)), inference(resolution, [status(thm)], [c_10084, c_16])).
% 7.36/2.80  tff(c_10014, plain, (![A_901, B_902, C_903]: (~r1_xboole_0(A_901, B_902) | ~r2_hidden(C_903, k3_xboole_0(A_901, B_902)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.36/2.80  tff(c_10028, plain, (![A_901, B_902]: (~r1_xboole_0(A_901, B_902) | v1_xboole_0(k3_xboole_0(A_901, B_902)))), inference(resolution, [status(thm)], [c_4, c_10014])).
% 7.36/2.80  tff(c_10104, plain, (![A_919]: (~r1_xboole_0(A_919, A_919) | v1_xboole_0(A_919))), inference(superposition, [status(thm), theory('equality')], [c_10089, c_10028])).
% 7.36/2.80  tff(c_10109, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_10104])).
% 7.36/2.80  tff(c_10438, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10431, c_10109])).
% 7.36/2.80  tff(c_10441, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10424, c_10438])).
% 7.36/2.80  tff(c_10443, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_10394])).
% 7.36/2.80  tff(c_10637, plain, (![A_968, B_969, C_970, D_971]: (k5_mcart_1(A_968, B_969, C_970, D_971)=k1_mcart_1(k1_mcart_1(D_971)) | ~m1_subset_1(D_971, k3_zfmisc_1(A_968, B_969, C_970)) | k1_xboole_0=C_970 | k1_xboole_0=B_969 | k1_xboole_0=A_968)), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.36/2.80  tff(c_10640, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_40, c_10637])).
% 7.36/2.80  tff(c_10643, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_10443, c_10640])).
% 7.36/2.80  tff(c_10883, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_10643])).
% 7.36/2.80  tff(c_10017, plain, (![C_903]: (~r1_xboole_0('#skF_8', '#skF_5') | ~r2_hidden(C_903, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_5698, c_10014])).
% 7.36/2.80  tff(c_10029, plain, (~r1_xboole_0('#skF_8', '#skF_5')), inference(splitLeft, [status(thm)], [c_10017])).
% 7.36/2.80  tff(c_10251, plain, (![A_941, B_942]: (r2_hidden('#skF_3'(A_941, B_942), k3_xboole_0(A_941, B_942)) | r1_xboole_0(A_941, B_942))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.36/2.80  tff(c_10268, plain, (r2_hidden('#skF_3'('#skF_8', '#skF_5'), '#skF_8') | r1_xboole_0('#skF_8', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5698, c_10251])).
% 7.36/2.80  tff(c_10279, plain, (r2_hidden('#skF_3'('#skF_8', '#skF_5'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_10029, c_10268])).
% 7.36/2.80  tff(c_10471, plain, (![B_956]: (r2_hidden('#skF_3'('#skF_8', '#skF_5'), B_956) | ~r1_tarski('#skF_8', B_956))), inference(resolution, [status(thm)], [c_10279, c_6])).
% 7.36/2.80  tff(c_10148, plain, (![A_924, C_925]: (~r1_xboole_0(A_924, A_924) | ~r2_hidden(C_925, A_924))), inference(superposition, [status(thm), theory('equality')], [c_10089, c_14])).
% 7.36/2.80  tff(c_10152, plain, (![C_925]: (~r2_hidden(C_925, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_10148])).
% 7.36/2.80  tff(c_10493, plain, (~r1_tarski('#skF_8', k1_xboole_0)), inference(resolution, [status(thm)], [c_10471, c_10152])).
% 7.36/2.80  tff(c_10887, plain, (~r1_tarski('#skF_8', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10883, c_10493])).
% 7.36/2.80  tff(c_10900, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5681, c_10887])).
% 7.36/2.80  tff(c_10902, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_10643])).
% 7.36/2.80  tff(c_10497, plain, (![A_957, B_958, C_959, D_960]: (k6_mcart_1(A_957, B_958, C_959, D_960)=k2_mcart_1(k1_mcart_1(D_960)) | ~m1_subset_1(D_960, k3_zfmisc_1(A_957, B_958, C_959)) | k1_xboole_0=C_959 | k1_xboole_0=B_958 | k1_xboole_0=A_957)), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.36/2.80  tff(c_10500, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_40, c_10497])).
% 7.36/2.80  tff(c_10503, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_10443, c_10500])).
% 7.36/2.80  tff(c_11004, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_10902, c_10503])).
% 7.36/2.80  tff(c_11005, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_11004])).
% 7.36/2.80  tff(c_10020, plain, (![C_903]: (~r1_xboole_0('#skF_9', '#skF_6') | ~r2_hidden(C_903, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_5699, c_10014])).
% 7.36/2.80  tff(c_10030, plain, (~r1_xboole_0('#skF_9', '#skF_6')), inference(splitLeft, [status(thm)], [c_10020])).
% 7.36/2.80  tff(c_10271, plain, (r2_hidden('#skF_3'('#skF_9', '#skF_6'), '#skF_9') | r1_xboole_0('#skF_9', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_5699, c_10251])).
% 7.36/2.80  tff(c_10280, plain, (r2_hidden('#skF_3'('#skF_9', '#skF_6'), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_10030, c_10271])).
% 7.36/2.80  tff(c_10523, plain, (![B_962]: (r2_hidden('#skF_3'('#skF_9', '#skF_6'), B_962) | ~r1_tarski('#skF_9', B_962))), inference(resolution, [status(thm)], [c_10280, c_6])).
% 7.36/2.80  tff(c_10545, plain, (~r1_tarski('#skF_9', k1_xboole_0)), inference(resolution, [status(thm)], [c_10523, c_10152])).
% 7.36/2.80  tff(c_11009, plain, (~r1_tarski('#skF_9', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11005, c_10545])).
% 7.36/2.80  tff(c_11024, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5679, c_11009])).
% 7.36/2.80  tff(c_11025, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')), inference(splitRight, [status(thm)], [c_11004])).
% 7.36/2.80  tff(c_10171, plain, (![A_928, B_929, C_930]: (r2_hidden(k1_mcart_1(A_928), B_929) | ~r2_hidden(A_928, k2_zfmisc_1(B_929, C_930)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.36/2.80  tff(c_11327, plain, (![A_1028, A_1029, B_1030, C_1031]: (r2_hidden(k1_mcart_1(A_1028), k2_zfmisc_1(A_1029, B_1030)) | ~r2_hidden(A_1028, k3_zfmisc_1(A_1029, B_1030, C_1031)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_10171])).
% 7.36/2.80  tff(c_11382, plain, (r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_38, c_11327])).
% 7.36/2.80  tff(c_11498, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')), '#skF_8')), inference(resolution, [status(thm)], [c_11382, c_26])).
% 7.36/2.80  tff(c_11506, plain, (r2_hidden(k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_11025, c_11498])).
% 7.36/2.80  tff(c_11508, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10008, c_11506])).
% 7.36/2.80  tff(c_11509, plain, (![C_903]: (~r2_hidden(C_903, '#skF_9'))), inference(splitRight, [status(thm)], [c_10020])).
% 7.36/2.80  tff(c_10009, plain, (r2_hidden(k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_9')), inference(splitRight, [status(thm)], [c_5667])).
% 7.36/2.80  tff(c_11512, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11509, c_10009])).
% 7.36/2.80  tff(c_11513, plain, (![C_903]: (~r2_hidden(C_903, '#skF_8'))), inference(splitRight, [status(thm)], [c_10017])).
% 7.36/2.80  tff(c_12627, plain, (![B_1125]: (v1_xboole_0(k2_zfmisc_1(B_1125, '#skF_8')))), inference(resolution, [status(thm)], [c_12592, c_11513])).
% 7.36/2.80  tff(c_12631, plain, (![B_1127]: (v1_xboole_0(k2_zfmisc_1(B_1127, '#skF_8')))), inference(resolution, [status(thm)], [c_12592, c_11513])).
% 7.36/2.80  tff(c_11538, plain, (![A_1042, B_1043]: (r2_hidden('#skF_2'(A_1042, B_1043), A_1042) | r1_tarski(A_1042, B_1043))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.36/2.80  tff(c_11624, plain, (![A_1051, B_1052]: (~v1_xboole_0(A_1051) | r1_tarski(A_1051, B_1052))), inference(resolution, [status(thm)], [c_11538, c_2])).
% 7.36/2.80  tff(c_11628, plain, (![A_1051, B_1052]: (k3_xboole_0(A_1051, B_1052)=A_1051 | ~v1_xboole_0(A_1051))), inference(resolution, [status(thm)], [c_11624, c_16])).
% 7.36/2.80  tff(c_12793, plain, (![B_1149, B_1150]: (k3_xboole_0(k2_zfmisc_1(B_1149, '#skF_8'), B_1150)=k2_zfmisc_1(B_1149, '#skF_8'))), inference(resolution, [status(thm)], [c_12631, c_11628])).
% 7.36/2.80  tff(c_11860, plain, (![A_1080, B_1081]: (r2_hidden('#skF_3'(A_1080, B_1081), k3_xboole_0(A_1080, B_1081)) | r1_xboole_0(A_1080, B_1081))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.36/2.80  tff(c_11886, plain, (![A_1080, B_1081]: (~v1_xboole_0(k3_xboole_0(A_1080, B_1081)) | r1_xboole_0(A_1080, B_1081))), inference(resolution, [status(thm)], [c_11860, c_2])).
% 7.36/2.80  tff(c_12805, plain, (![B_1149, B_1150]: (~v1_xboole_0(k2_zfmisc_1(B_1149, '#skF_8')) | r1_xboole_0(k2_zfmisc_1(B_1149, '#skF_8'), B_1150))), inference(superposition, [status(thm), theory('equality')], [c_12793, c_11886])).
% 7.36/2.80  tff(c_12841, plain, (![B_1151, B_1152]: (r1_xboole_0(k2_zfmisc_1(B_1151, '#skF_8'), B_1152))), inference(demodulation, [status(thm), theory('equality')], [c_12627, c_12805])).
% 7.36/2.80  tff(c_11558, plain, (![A_1044]: (r1_tarski(A_1044, A_1044))), inference(resolution, [status(thm)], [c_11538, c_8])).
% 7.36/2.80  tff(c_11569, plain, (![A_1046]: (k3_xboole_0(A_1046, A_1046)=A_1046)), inference(resolution, [status(thm)], [c_11558, c_16])).
% 7.36/2.80  tff(c_11578, plain, (![A_1046, C_14]: (~r1_xboole_0(A_1046, A_1046) | ~r2_hidden(C_14, A_1046))), inference(superposition, [status(thm), theory('equality')], [c_11569, c_14])).
% 7.36/2.80  tff(c_12949, plain, (![C_1159, B_1160]: (~r2_hidden(C_1159, k2_zfmisc_1(B_1160, '#skF_8')))), inference(resolution, [status(thm)], [c_12841, c_11578])).
% 7.36/2.80  tff(c_12957, plain, (![B_1160, C_1056]: (v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(B_1160, '#skF_8'), C_1056)))), inference(resolution, [status(thm)], [c_11645, c_12949])).
% 7.36/2.80  tff(c_13000, plain, (![B_1160, C_1056]: (v1_xboole_0(k3_zfmisc_1(B_1160, '#skF_8', C_1056)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_12957])).
% 7.36/2.80  tff(c_13024, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13000, c_52])).
% 7.36/2.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.36/2.80  
% 7.36/2.80  Inference rules
% 7.36/2.80  ----------------------
% 7.36/2.80  #Ref     : 0
% 7.36/2.80  #Sup     : 2846
% 7.36/2.80  #Fact    : 0
% 7.36/2.80  #Define  : 0
% 7.36/2.80  #Split   : 69
% 7.36/2.80  #Chain   : 0
% 7.36/2.80  #Close   : 0
% 7.36/2.80  
% 7.36/2.80  Ordering : KBO
% 7.36/2.80  
% 7.36/2.80  Simplification rules
% 7.36/2.80  ----------------------
% 7.36/2.80  #Subsume      : 795
% 7.36/2.80  #Demod        : 989
% 7.36/2.80  #Tautology    : 723
% 7.36/2.80  #SimpNegUnit  : 118
% 7.36/2.80  #BackRed      : 249
% 7.36/2.80  
% 7.36/2.80  #Partial instantiations: 0
% 7.36/2.80  #Strategies tried      : 1
% 7.36/2.80  
% 7.36/2.80  Timing (in seconds)
% 7.36/2.80  ----------------------
% 7.36/2.80  Preprocessing        : 0.32
% 7.36/2.81  Parsing              : 0.17
% 7.36/2.81  CNF conversion       : 0.02
% 7.36/2.81  Main loop            : 1.62
% 7.36/2.81  Inferencing          : 0.56
% 7.36/2.81  Reduction            : 0.54
% 7.36/2.81  Demodulation         : 0.35
% 7.36/2.81  BG Simplification    : 0.05
% 7.36/2.81  Subsumption          : 0.31
% 7.36/2.81  Abstraction          : 0.07
% 7.36/2.81  MUC search           : 0.00
% 7.36/2.81  Cooper               : 0.00
% 7.36/2.81  Total                : 2.03
% 7.36/2.81  Index Insertion      : 0.00
% 7.36/2.81  Index Deletion       : 0.00
% 7.36/2.81  Index Matching       : 0.00
% 7.36/2.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
