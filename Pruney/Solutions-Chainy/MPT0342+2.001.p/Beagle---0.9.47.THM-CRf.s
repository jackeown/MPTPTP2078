%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:16 EST 2020

% Result     : Theorem 23.27s
% Output     : CNFRefutation 23.30s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 518 expanded)
%              Number of leaves         :   22 ( 174 expanded)
%              Depth                    :   12
%              Number of atoms          :  337 (1495 expanded)
%              Number of equality atoms :   59 ( 260 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( ! [D] :
                  ( m1_subset_1(D,A)
                 => ( r2_hidden(D,B)
                   => r2_hidden(D,C) ) )
             => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_42,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_78,plain,(
    ! [B_36,A_37] :
      ( r2_hidden(B_36,A_37)
      | ~ m1_subset_1(B_36,A_37)
      | v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_44,plain,(
    ! [D_26] :
      ( r2_hidden(D_26,'#skF_6')
      | ~ r2_hidden(D_26,'#skF_5')
      | ~ m1_subset_1(D_26,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_86,plain,(
    ! [B_36] :
      ( r2_hidden(B_36,'#skF_6')
      | ~ m1_subset_1(B_36,'#skF_4')
      | ~ m1_subset_1(B_36,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_78,c_44])).

tff(c_19030,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_21490,plain,(
    ! [A_928,B_929,C_930] :
      ( r2_hidden('#skF_2'(A_928,B_929,C_930),B_929)
      | r2_hidden('#skF_2'(A_928,B_929,C_930),A_928)
      | r2_hidden('#skF_3'(A_928,B_929,C_930),C_930)
      | k2_xboole_0(A_928,B_929) = C_930 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_20,plain,(
    ! [A_5,B_6,C_7] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6,C_7),C_7)
      | r2_hidden('#skF_3'(A_5,B_6,C_7),C_7)
      | k2_xboole_0(A_5,B_6) = C_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_21712,plain,(
    ! [A_946,B_947] :
      ( r2_hidden('#skF_2'(A_946,B_947,B_947),A_946)
      | r2_hidden('#skF_3'(A_946,B_947,B_947),B_947)
      | k2_xboole_0(A_946,B_947) = B_947 ) ),
    inference(resolution,[status(thm)],[c_21490,c_20])).

tff(c_21047,plain,(
    ! [A_909,B_910,C_911] :
      ( r2_hidden('#skF_2'(A_909,B_910,C_911),B_910)
      | r2_hidden('#skF_2'(A_909,B_910,C_911),A_909)
      | ~ r2_hidden('#skF_3'(A_909,B_910,C_911),B_910)
      | k2_xboole_0(A_909,B_910) = C_911 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_12,plain,(
    ! [A_5,B_6,C_7] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6,C_7),C_7)
      | ~ r2_hidden('#skF_3'(A_5,B_6,C_7),B_6)
      | k2_xboole_0(A_5,B_6) = C_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_21101,plain,(
    ! [A_909,B_910] :
      ( r2_hidden('#skF_2'(A_909,B_910,B_910),A_909)
      | ~ r2_hidden('#skF_3'(A_909,B_910,B_910),B_910)
      | k2_xboole_0(A_909,B_910) = B_910 ) ),
    inference(resolution,[status(thm)],[c_21047,c_12])).

tff(c_21963,plain,(
    ! [A_950,B_951] :
      ( r2_hidden('#skF_2'(A_950,B_951,B_951),A_950)
      | k2_xboole_0(A_950,B_951) = B_951 ) ),
    inference(resolution,[status(thm)],[c_21712,c_21101])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22001,plain,(
    ! [A_952,B_953] :
      ( ~ v1_xboole_0(A_952)
      | k2_xboole_0(A_952,B_953) = B_953 ) ),
    inference(resolution,[status(thm)],[c_21963,c_2])).

tff(c_22015,plain,(
    ! [B_954] : k2_xboole_0('#skF_5',B_954) = B_954 ),
    inference(resolution,[status(thm)],[c_19030,c_22001])).

tff(c_28,plain,(
    ! [B_12] : r1_tarski(B_12,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_19034,plain,(
    ! [A_736,C_737,B_738] :
      ( r1_tarski(A_736,C_737)
      | ~ r1_tarski(k2_xboole_0(A_736,B_738),C_737) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_19039,plain,(
    ! [A_736,B_738] : r1_tarski(A_736,k2_xboole_0(A_736,B_738)) ),
    inference(resolution,[status(thm)],[c_28,c_19034])).

tff(c_22062,plain,(
    ! [B_954] : r1_tarski('#skF_5',B_954) ),
    inference(superposition,[status(thm),theory(equality)],[c_22015,c_19039])).

tff(c_22094,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22062,c_42])).

tff(c_22096,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_23039,plain,(
    ! [A_1075,B_1076,C_1077] :
      ( r2_hidden('#skF_2'(A_1075,B_1076,C_1077),B_1076)
      | r2_hidden('#skF_2'(A_1075,B_1076,C_1077),A_1075)
      | r2_hidden('#skF_3'(A_1075,B_1076,C_1077),C_1077)
      | k2_xboole_0(A_1075,B_1076) = C_1077 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_25588,plain,(
    ! [A_1152,B_1153] :
      ( r2_hidden('#skF_2'(A_1152,B_1153,B_1153),A_1152)
      | r2_hidden('#skF_3'(A_1152,B_1153,B_1153),B_1153)
      | k2_xboole_0(A_1152,B_1153) = B_1153 ) ),
    inference(resolution,[status(thm)],[c_23039,c_20])).

tff(c_23286,plain,(
    ! [A_1083,B_1084,C_1085] :
      ( r2_hidden('#skF_2'(A_1083,B_1084,C_1085),B_1084)
      | r2_hidden('#skF_2'(A_1083,B_1084,C_1085),A_1083)
      | ~ r2_hidden('#skF_3'(A_1083,B_1084,C_1085),B_1084)
      | k2_xboole_0(A_1083,B_1084) = C_1085 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_23339,plain,(
    ! [A_1083,B_1084] :
      ( r2_hidden('#skF_2'(A_1083,B_1084,B_1084),A_1083)
      | ~ r2_hidden('#skF_3'(A_1083,B_1084,B_1084),B_1084)
      | k2_xboole_0(A_1083,B_1084) = B_1084 ) ),
    inference(resolution,[status(thm)],[c_23286,c_12])).

tff(c_25658,plain,(
    ! [A_1154,B_1155] :
      ( r2_hidden('#skF_2'(A_1154,B_1155,B_1155),A_1154)
      | k2_xboole_0(A_1154,B_1155) = B_1155 ) ),
    inference(resolution,[status(thm)],[c_25588,c_23339])).

tff(c_32,plain,(
    ! [B_17,A_16] :
      ( m1_subset_1(B_17,A_16)
      | ~ r2_hidden(B_17,A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_47921,plain,(
    ! [A_1755,B_1756] :
      ( m1_subset_1('#skF_2'(A_1755,B_1756,B_1756),A_1755)
      | v1_xboole_0(A_1755)
      | k2_xboole_0(A_1755,B_1756) = B_1756 ) ),
    inference(resolution,[status(thm)],[c_25658,c_32])).

tff(c_16327,plain,(
    ! [A_643,B_644,C_645] :
      ( r2_hidden('#skF_2'(A_643,B_644,C_645),B_644)
      | r2_hidden('#skF_2'(A_643,B_644,C_645),A_643)
      | r2_hidden('#skF_3'(A_643,B_644,C_645),C_645)
      | k2_xboole_0(A_643,B_644) = C_645 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_18179,plain,(
    ! [A_722,B_723] :
      ( r2_hidden('#skF_2'(A_722,B_723,B_723),A_722)
      | r2_hidden('#skF_3'(A_722,B_723,B_723),B_723)
      | k2_xboole_0(A_722,B_723) = B_723 ) ),
    inference(resolution,[status(thm)],[c_16327,c_20])).

tff(c_16678,plain,(
    ! [A_662,B_663,C_664] :
      ( r2_hidden('#skF_2'(A_662,B_663,C_664),B_663)
      | r2_hidden('#skF_2'(A_662,B_663,C_664),A_662)
      | ~ r2_hidden('#skF_3'(A_662,B_663,C_664),B_663)
      | k2_xboole_0(A_662,B_663) = C_664 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_16731,plain,(
    ! [A_662,B_663] :
      ( r2_hidden('#skF_2'(A_662,B_663,B_663),A_662)
      | ~ r2_hidden('#skF_3'(A_662,B_663,B_663),B_663)
      | k2_xboole_0(A_662,B_663) = B_663 ) ),
    inference(resolution,[status(thm)],[c_16678,c_12])).

tff(c_18574,plain,(
    ! [A_726,B_727] :
      ( r2_hidden('#skF_2'(A_726,B_727,B_727),A_726)
      | k2_xboole_0(A_726,B_727) = B_727 ) ),
    inference(resolution,[status(thm)],[c_18179,c_16731])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    ! [D_35] :
      ( r2_hidden(D_35,'#skF_6')
      | ~ r2_hidden(D_35,'#skF_5')
      | ~ m1_subset_1(D_35,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_77,plain,
    ( r2_hidden('#skF_1'('#skF_5'),'#skF_6')
    | ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_72])).

tff(c_128,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_3351,plain,(
    ! [A_271,B_272,C_273] :
      ( r2_hidden('#skF_2'(A_271,B_272,C_273),B_272)
      | r2_hidden('#skF_2'(A_271,B_272,C_273),A_271)
      | r2_hidden('#skF_3'(A_271,B_272,C_273),C_273)
      | k2_xboole_0(A_271,B_272) = C_273 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_14487,plain,(
    ! [A_490,B_491] :
      ( r2_hidden('#skF_2'(A_490,B_491,A_490),B_491)
      | r2_hidden('#skF_3'(A_490,B_491,A_490),A_490)
      | k2_xboole_0(A_490,B_491) = A_490 ) ),
    inference(resolution,[status(thm)],[c_3351,c_20])).

tff(c_14545,plain,(
    ! [B_492] :
      ( r2_hidden('#skF_3'(B_492,B_492,B_492),B_492)
      | k2_xboole_0(B_492,B_492) = B_492 ) ),
    inference(resolution,[status(thm)],[c_14487,c_20])).

tff(c_14,plain,(
    ! [A_5,B_6,C_7] :
      ( r2_hidden('#skF_2'(A_5,B_6,C_7),B_6)
      | r2_hidden('#skF_2'(A_5,B_6,C_7),A_5)
      | ~ r2_hidden('#skF_3'(A_5,B_6,C_7),B_6)
      | k2_xboole_0(A_5,B_6) = C_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_14315,plain,(
    ! [A_478,C_479] :
      ( ~ r2_hidden('#skF_3'(A_478,A_478,C_479),A_478)
      | k2_xboole_0(A_478,A_478) = C_479
      | r2_hidden('#skF_2'(A_478,A_478,C_479),A_478) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_14])).

tff(c_14342,plain,(
    ! [A_478] :
      ( ~ r2_hidden('#skF_3'(A_478,A_478,A_478),A_478)
      | k2_xboole_0(A_478,A_478) = A_478 ) ),
    inference(resolution,[status(thm)],[c_14315,c_12])).

tff(c_14567,plain,(
    ! [B_492] : k2_xboole_0(B_492,B_492) = B_492 ),
    inference(resolution,[status(thm)],[c_14545,c_14342])).

tff(c_3420,plain,(
    ! [A_271,B_272] :
      ( r2_hidden('#skF_2'(A_271,B_272,B_272),A_271)
      | r2_hidden('#skF_3'(A_271,B_272,B_272),B_272)
      | k2_xboole_0(A_271,B_272) = B_272 ) ),
    inference(resolution,[status(thm)],[c_3351,c_20])).

tff(c_4297,plain,(
    ! [A_297,B_298,C_299] :
      ( r2_hidden('#skF_2'(A_297,B_298,C_299),B_298)
      | r2_hidden('#skF_2'(A_297,B_298,C_299),A_297)
      | ~ r2_hidden('#skF_3'(A_297,B_298,C_299),B_298)
      | k2_xboole_0(A_297,B_298) = C_299 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_9961,plain,(
    ! [A_385,B_386] :
      ( r2_hidden('#skF_2'(A_385,B_386,B_386),A_385)
      | ~ r2_hidden('#skF_3'(A_385,B_386,B_386),B_386)
      | k2_xboole_0(A_385,B_386) = B_386 ) ),
    inference(resolution,[status(thm)],[c_4297,c_12])).

tff(c_13877,plain,(
    ! [A_468,B_469] :
      ( r2_hidden('#skF_2'(A_468,B_469,B_469),A_468)
      | k2_xboole_0(A_468,B_469) = B_469 ) ),
    inference(resolution,[status(thm)],[c_3420,c_9961])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_22,plain,(
    ! [A_5,B_6,C_7] :
      ( r2_hidden('#skF_2'(A_5,B_6,C_7),B_6)
      | r2_hidden('#skF_2'(A_5,B_6,C_7),A_5)
      | r2_hidden('#skF_3'(A_5,B_6,C_7),C_7)
      | k2_xboole_0(A_5,B_6) = C_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3990,plain,(
    ! [A_291,C_292] :
      ( r2_hidden('#skF_3'(A_291,A_291,C_292),C_292)
      | k2_xboole_0(A_291,A_291) = C_292
      | r2_hidden('#skF_2'(A_291,A_291,C_292),A_291) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_22])).

tff(c_4046,plain,(
    ! [A_293] :
      ( r2_hidden('#skF_3'(A_293,A_293,A_293),A_293)
      | k2_xboole_0(A_293,A_293) = A_293 ) ),
    inference(resolution,[status(thm)],[c_3990,c_20])).

tff(c_3848,plain,(
    ! [A_286,C_287] :
      ( ~ r2_hidden('#skF_3'(A_286,A_286,C_287),A_286)
      | k2_xboole_0(A_286,A_286) = C_287
      | r2_hidden('#skF_2'(A_286,A_286,C_287),A_286) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_14])).

tff(c_3876,plain,(
    ! [A_286] :
      ( ~ r2_hidden('#skF_3'(A_286,A_286,A_286),A_286)
      | k2_xboole_0(A_286,A_286) = A_286 ) ),
    inference(resolution,[status(thm)],[c_3848,c_12])).

tff(c_4068,plain,(
    ! [A_293] : k2_xboole_0(A_293,A_293) = A_293 ),
    inference(resolution,[status(thm)],[c_4046,c_3876])).

tff(c_36,plain,(
    ! [B_17,A_16] :
      ( m1_subset_1(B_17,A_16)
      | ~ v1_xboole_0(B_17)
      | ~ v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_132,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_5'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_128])).

tff(c_133,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_141,plain,(
    ! [C_58,A_59,B_60] :
      ( r2_hidden(C_58,A_59)
      | ~ r2_hidden(C_58,B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_183,plain,(
    ! [A_72,A_73] :
      ( r2_hidden('#skF_1'(A_72),A_73)
      | ~ m1_subset_1(A_72,k1_zfmisc_1(A_73))
      | v1_xboole_0(A_72) ) ),
    inference(resolution,[status(thm)],[c_4,c_141])).

tff(c_197,plain,(
    ! [A_72,A_73] :
      ( m1_subset_1('#skF_1'(A_72),A_73)
      | v1_xboole_0(A_73)
      | ~ m1_subset_1(A_72,k1_zfmisc_1(A_73))
      | v1_xboole_0(A_72) ) ),
    inference(resolution,[status(thm)],[c_183,c_32])).

tff(c_221,plain,(
    ! [D_77,B_78,A_79] :
      ( r2_hidden(D_77,B_78)
      | r2_hidden(D_77,A_79)
      | ~ r2_hidden(D_77,k2_xboole_0(A_79,B_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_244,plain,(
    ! [A_79,B_78] :
      ( r2_hidden('#skF_1'(k2_xboole_0(A_79,B_78)),B_78)
      | r2_hidden('#skF_1'(k2_xboole_0(A_79,B_78)),A_79)
      | v1_xboole_0(k2_xboole_0(A_79,B_78)) ) ),
    inference(resolution,[status(thm)],[c_4,c_221])).

tff(c_3513,plain,(
    ! [B_278] :
      ( v1_xboole_0(k2_xboole_0(B_278,B_278))
      | r2_hidden('#skF_1'(k2_xboole_0(B_278,B_278)),B_278) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_244])).

tff(c_3533,plain,
    ( r2_hidden('#skF_1'(k2_xboole_0('#skF_5','#skF_5')),'#skF_6')
    | ~ m1_subset_1('#skF_1'(k2_xboole_0('#skF_5','#skF_5')),'#skF_4')
    | v1_xboole_0(k2_xboole_0('#skF_5','#skF_5')) ),
    inference(resolution,[status(thm)],[c_3513,c_44])).

tff(c_3535,plain,(
    ~ m1_subset_1('#skF_1'(k2_xboole_0('#skF_5','#skF_5')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3533])).

tff(c_3551,plain,
    ( v1_xboole_0('#skF_4')
    | ~ m1_subset_1(k2_xboole_0('#skF_5','#skF_5'),k1_zfmisc_1('#skF_4'))
    | v1_xboole_0(k2_xboole_0('#skF_5','#skF_5')) ),
    inference(resolution,[status(thm)],[c_197,c_3535])).

tff(c_3559,plain,
    ( ~ m1_subset_1(k2_xboole_0('#skF_5','#skF_5'),k1_zfmisc_1('#skF_4'))
    | v1_xboole_0(k2_xboole_0('#skF_5','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_3551])).

tff(c_3561,plain,(
    ~ m1_subset_1(k2_xboole_0('#skF_5','#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3559])).

tff(c_4082,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4068,c_3561])).

tff(c_4089,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4082])).

tff(c_4090,plain,(
    v1_xboole_0(k2_xboole_0('#skF_5','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_3559])).

tff(c_119,plain,(
    ! [D_49,B_50,A_51] :
      ( ~ r2_hidden(D_49,B_50)
      | r2_hidden(D_49,k2_xboole_0(A_51,B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_127,plain,(
    ! [A_51,B_50,D_49] :
      ( ~ v1_xboole_0(k2_xboole_0(A_51,B_50))
      | ~ r2_hidden(D_49,B_50) ) ),
    inference(resolution,[status(thm)],[c_119,c_2])).

tff(c_4096,plain,(
    ! [D_49] : ~ r2_hidden(D_49,'#skF_5') ),
    inference(resolution,[status(thm)],[c_4090,c_127])).

tff(c_13968,plain,(
    ! [B_470] : k2_xboole_0('#skF_5',B_470) = B_470 ),
    inference(resolution,[status(thm)],[c_13877,c_4096])).

tff(c_135,plain,(
    ! [A_55,C_56,B_57] :
      ( r1_tarski(A_55,C_56)
      | ~ r1_tarski(k2_xboole_0(A_55,B_57),C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_140,plain,(
    ! [A_55,B_57] : r1_tarski(A_55,k2_xboole_0(A_55,B_57)) ),
    inference(resolution,[status(thm)],[c_28,c_135])).

tff(c_14078,plain,(
    ! [B_470] : r1_tarski('#skF_5',B_470) ),
    inference(superposition,[status(thm),theory(equality)],[c_13968,c_140])).

tff(c_14135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14078,c_42])).

tff(c_14137,plain,(
    m1_subset_1('#skF_1'(k2_xboole_0('#skF_5','#skF_5')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_3533])).

tff(c_14581,plain,(
    m1_subset_1('#skF_1'('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14567,c_14137])).

tff(c_14585,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_14581])).

tff(c_14587,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_14637,plain,(
    ! [D_513,B_514,A_515] :
      ( r2_hidden(D_513,B_514)
      | r2_hidden(D_513,A_515)
      | ~ r2_hidden(D_513,k2_xboole_0(A_515,B_514)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_14655,plain,(
    ! [A_515,B_514] :
      ( r2_hidden('#skF_1'(k2_xboole_0(A_515,B_514)),B_514)
      | r2_hidden('#skF_1'(k2_xboole_0(A_515,B_514)),A_515)
      | v1_xboole_0(k2_xboole_0(A_515,B_514)) ) ),
    inference(resolution,[status(thm)],[c_4,c_14637])).

tff(c_16747,plain,(
    ! [B_665] :
      ( v1_xboole_0(k2_xboole_0(B_665,B_665))
      | r2_hidden('#skF_1'(k2_xboole_0(B_665,B_665)),B_665) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_14655])).

tff(c_40,plain,(
    ! [C_21,A_18,B_19] :
      ( r2_hidden(C_21,A_18)
      | ~ r2_hidden(C_21,B_19)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_17361,plain,(
    ! [B_696,A_697] :
      ( r2_hidden('#skF_1'(k2_xboole_0(B_696,B_696)),A_697)
      | ~ m1_subset_1(B_696,k1_zfmisc_1(A_697))
      | v1_xboole_0(k2_xboole_0(B_696,B_696)) ) ),
    inference(resolution,[status(thm)],[c_16747,c_40])).

tff(c_17383,plain,(
    ! [A_698,B_699] :
      ( ~ v1_xboole_0(A_698)
      | ~ m1_subset_1(B_699,k1_zfmisc_1(A_698))
      | v1_xboole_0(k2_xboole_0(B_699,B_699)) ) ),
    inference(resolution,[status(thm)],[c_17361,c_2])).

tff(c_17406,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0(k2_xboole_0('#skF_5','#skF_5')) ),
    inference(resolution,[status(thm)],[c_48,c_17383])).

tff(c_17418,plain,(
    v1_xboole_0(k2_xboole_0('#skF_5','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14587,c_17406])).

tff(c_17426,plain,(
    ! [D_49] : ~ r2_hidden(D_49,'#skF_5') ),
    inference(resolution,[status(thm)],[c_17418,c_127])).

tff(c_18866,plain,(
    ! [B_732] : k2_xboole_0('#skF_5',B_732) = B_732 ),
    inference(resolution,[status(thm)],[c_18574,c_17426])).

tff(c_14590,plain,(
    ! [A_496,C_497,B_498] :
      ( r1_tarski(A_496,C_497)
      | ~ r1_tarski(k2_xboole_0(A_496,B_498),C_497) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14595,plain,(
    ! [A_496,B_498] : r1_tarski(A_496,k2_xboole_0(A_496,B_498)) ),
    inference(resolution,[status(thm)],[c_28,c_14590])).

tff(c_18961,plain,(
    ! [B_732] : r1_tarski('#skF_5',B_732) ),
    inference(superposition,[status(thm),theory(equality)],[c_18866,c_14595])).

tff(c_19023,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18961,c_42])).

tff(c_19025,plain,(
    m1_subset_1('#skF_1'('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_38,plain,(
    ! [B_17,A_16] :
      ( v1_xboole_0(B_17)
      | ~ m1_subset_1(B_17,A_16)
      | ~ v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_19029,plain,
    ( v1_xboole_0('#skF_1'('#skF_5'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_19025,c_38])).

tff(c_22112,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_19029])).

tff(c_34,plain,(
    ! [B_17,A_16] :
      ( r2_hidden(B_17,A_16)
      | ~ m1_subset_1(B_17,A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_22148,plain,(
    ! [C_967,A_968,B_969] :
      ( r2_hidden(C_967,A_968)
      | ~ r2_hidden(C_967,B_969)
      | ~ m1_subset_1(B_969,k1_zfmisc_1(A_968)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_22365,plain,(
    ! [B_1008,A_1009,A_1010] :
      ( r2_hidden(B_1008,A_1009)
      | ~ m1_subset_1(A_1010,k1_zfmisc_1(A_1009))
      | ~ m1_subset_1(B_1008,A_1010)
      | v1_xboole_0(A_1010) ) ),
    inference(resolution,[status(thm)],[c_34,c_22148])).

tff(c_22376,plain,(
    ! [B_1008] :
      ( r2_hidden(B_1008,'#skF_4')
      | ~ m1_subset_1(B_1008,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_22365])).

tff(c_22388,plain,(
    ! [B_1011] :
      ( r2_hidden(B_1011,'#skF_4')
      | ~ m1_subset_1(B_1011,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_22096,c_22376])).

tff(c_22393,plain,(
    ! [B_1011] :
      ( m1_subset_1(B_1011,'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(B_1011,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22388,c_32])).

tff(c_22400,plain,(
    ! [B_1011] :
      ( m1_subset_1(B_1011,'#skF_4')
      | ~ m1_subset_1(B_1011,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_22112,c_22393])).

tff(c_47963,plain,(
    ! [B_1756] :
      ( m1_subset_1('#skF_2'('#skF_5',B_1756,B_1756),'#skF_4')
      | v1_xboole_0('#skF_5')
      | k2_xboole_0('#skF_5',B_1756) = B_1756 ) ),
    inference(resolution,[status(thm)],[c_47921,c_22400])).

tff(c_47996,plain,(
    ! [B_1756] :
      ( m1_subset_1('#skF_2'('#skF_5',B_1756,B_1756),'#skF_4')
      | k2_xboole_0('#skF_5',B_1756) = B_1756 ) ),
    inference(negUnitSimplification,[status(thm)],[c_22096,c_47963])).

tff(c_25699,plain,(
    ! [B_1155] :
      ( r2_hidden('#skF_2'('#skF_5',B_1155,B_1155),'#skF_6')
      | ~ m1_subset_1('#skF_2'('#skF_5',B_1155,B_1155),'#skF_4')
      | k2_xboole_0('#skF_5',B_1155) = B_1155 ) ),
    inference(resolution,[status(thm)],[c_25658,c_44])).

tff(c_23585,plain,(
    ! [A_1100,B_1101] :
      ( r2_hidden('#skF_2'(A_1100,B_1101,A_1100),B_1101)
      | r2_hidden('#skF_3'(A_1100,B_1101,A_1100),A_1100)
      | k2_xboole_0(A_1100,B_1101) = A_1100 ) ),
    inference(resolution,[status(thm)],[c_23039,c_20])).

tff(c_23695,plain,(
    ! [B_1104] :
      ( r2_hidden('#skF_3'(B_1104,B_1104,B_1104),B_1104)
      | k2_xboole_0(B_1104,B_1104) = B_1104 ) ),
    inference(resolution,[status(thm)],[c_23585,c_20])).

tff(c_23416,plain,(
    ! [A_1094,C_1095] :
      ( ~ r2_hidden('#skF_3'(A_1094,A_1094,C_1095),A_1094)
      | k2_xboole_0(A_1094,A_1094) = C_1095
      | r2_hidden('#skF_2'(A_1094,A_1094,C_1095),A_1094) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_14])).

tff(c_23443,plain,(
    ! [A_1094] :
      ( ~ r2_hidden('#skF_3'(A_1094,A_1094,A_1094),A_1094)
      | k2_xboole_0(A_1094,A_1094) = A_1094 ) ),
    inference(resolution,[status(thm)],[c_23416,c_12])).

tff(c_23715,plain,(
    ! [B_1104] : k2_xboole_0(B_1104,B_1104) = B_1104 ),
    inference(resolution,[status(thm)],[c_23695,c_23443])).

tff(c_10,plain,(
    ! [D_10,A_5,B_6] :
      ( ~ r2_hidden(D_10,A_5)
      | r2_hidden(D_10,k2_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_22402,plain,(
    ! [A_1012,B_1013,C_1014] :
      ( ~ r2_hidden('#skF_2'(A_1012,B_1013,C_1014),C_1014)
      | r2_hidden('#skF_3'(A_1012,B_1013,C_1014),C_1014)
      | k2_xboole_0(A_1012,B_1013) = C_1014 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_56158,plain,(
    ! [A_1925,B_1926,A_1927,B_1928] :
      ( r2_hidden('#skF_3'(A_1925,B_1926,k2_xboole_0(A_1927,B_1928)),k2_xboole_0(A_1927,B_1928))
      | k2_xboole_0(A_1927,B_1928) = k2_xboole_0(A_1925,B_1926)
      | ~ r2_hidden('#skF_2'(A_1925,B_1926,k2_xboole_0(A_1927,B_1928)),A_1927) ) ),
    inference(resolution,[status(thm)],[c_10,c_22402])).

tff(c_22621,plain,(
    ! [A_1039,B_1040,C_1041] :
      ( ~ r2_hidden('#skF_2'(A_1039,B_1040,C_1041),C_1041)
      | ~ r2_hidden('#skF_3'(A_1039,B_1040,C_1041),B_1040)
      | k2_xboole_0(A_1039,B_1040) = C_1041 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_22644,plain,(
    ! [A_1039,B_1040,A_5,B_6] :
      ( ~ r2_hidden('#skF_3'(A_1039,B_1040,k2_xboole_0(A_5,B_6)),B_1040)
      | k2_xboole_0(A_5,B_6) = k2_xboole_0(A_1039,B_1040)
      | ~ r2_hidden('#skF_2'(A_1039,B_1040,k2_xboole_0(A_5,B_6)),A_5) ) ),
    inference(resolution,[status(thm)],[c_10,c_22621])).

tff(c_73770,plain,(
    ! [A_2220,A_2221,B_2222] :
      ( k2_xboole_0(A_2220,k2_xboole_0(A_2221,B_2222)) = k2_xboole_0(A_2221,B_2222)
      | ~ r2_hidden('#skF_2'(A_2220,k2_xboole_0(A_2221,B_2222),k2_xboole_0(A_2221,B_2222)),A_2221) ) ),
    inference(resolution,[status(thm)],[c_56158,c_22644])).

tff(c_74016,plain,(
    ! [A_2220,B_1104] :
      ( k2_xboole_0(A_2220,k2_xboole_0(B_1104,B_1104)) = k2_xboole_0(B_1104,B_1104)
      | ~ r2_hidden('#skF_2'(A_2220,k2_xboole_0(B_1104,B_1104),B_1104),B_1104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23715,c_73770])).

tff(c_81117,plain,(
    ! [A_2281,B_2282] :
      ( k2_xboole_0(A_2281,B_2282) = B_2282
      | ~ r2_hidden('#skF_2'(A_2281,B_2282,B_2282),B_2282) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23715,c_23715,c_23715,c_74016])).

tff(c_81628,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_6'),'#skF_4')
    | k2_xboole_0('#skF_5','#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_25699,c_81117])).

tff(c_82347,plain,(
    ~ m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_6'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_81628])).

tff(c_82354,plain,(
    k2_xboole_0('#skF_5','#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_47996,c_82347])).

tff(c_22097,plain,(
    ! [A_955,C_956,B_957] :
      ( r1_tarski(A_955,C_956)
      | ~ r1_tarski(k2_xboole_0(A_955,B_957),C_956) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_22102,plain,(
    ! [A_955,B_957] : r1_tarski(A_955,k2_xboole_0(A_955,B_957)) ),
    inference(resolution,[status(thm)],[c_28,c_22097])).

tff(c_82847,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_82354,c_22102])).

tff(c_82954,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_82847])).

tff(c_82955,plain,(
    k2_xboole_0('#skF_5','#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_81628])).

tff(c_83260,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_82955,c_22102])).

tff(c_83367,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_83260])).

tff(c_83369,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_19029])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_19024,plain,
    ( v1_xboole_0('#skF_5')
    | r2_hidden('#skF_1'('#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_83370,plain,(
    r2_hidden('#skF_1'('#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_22096,c_19024])).

tff(c_83395,plain,(
    ! [C_2295,A_2296,B_2297] :
      ( r2_hidden(C_2295,A_2296)
      | ~ r2_hidden(C_2295,B_2297)
      | ~ m1_subset_1(B_2297,k1_zfmisc_1(A_2296)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_83411,plain,(
    ! [A_2298] :
      ( r2_hidden('#skF_1'('#skF_5'),A_2298)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_2298)) ) ),
    inference(resolution,[status(thm)],[c_83370,c_83395])).

tff(c_83430,plain,(
    ! [A_2299] :
      ( ~ v1_xboole_0(A_2299)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_2299)) ) ),
    inference(resolution,[status(thm)],[c_83411,c_2])).

tff(c_83436,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_83430])).

tff(c_83441,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83369,c_83436])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:40:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.27/13.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.30/13.67  
% 23.30/13.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.30/13.67  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 23.30/13.67  
% 23.30/13.67  %Foreground sorts:
% 23.30/13.67  
% 23.30/13.67  
% 23.30/13.67  %Background operators:
% 23.30/13.67  
% 23.30/13.67  
% 23.30/13.67  %Foreground operators:
% 23.30/13.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 23.30/13.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 23.30/13.67  tff('#skF_1', type, '#skF_1': $i > $i).
% 23.30/13.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 23.30/13.67  tff('#skF_5', type, '#skF_5': $i).
% 23.30/13.67  tff('#skF_6', type, '#skF_6': $i).
% 23.30/13.67  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 23.30/13.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 23.30/13.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 23.30/13.67  tff('#skF_4', type, '#skF_4': $i).
% 23.30/13.67  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 23.30/13.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 23.30/13.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 23.30/13.67  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 23.30/13.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 23.30/13.67  
% 23.30/13.69  tff(f_85, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_subset_1)).
% 23.30/13.69  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 23.30/13.69  tff(f_40, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 23.30/13.69  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 23.30/13.69  tff(f_46, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 23.30/13.69  tff(f_50, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 23.30/13.69  tff(f_70, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 23.30/13.69  tff(c_42, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_85])).
% 23.30/13.69  tff(c_78, plain, (![B_36, A_37]: (r2_hidden(B_36, A_37) | ~m1_subset_1(B_36, A_37) | v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_63])).
% 23.30/13.69  tff(c_44, plain, (![D_26]: (r2_hidden(D_26, '#skF_6') | ~r2_hidden(D_26, '#skF_5') | ~m1_subset_1(D_26, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 23.30/13.69  tff(c_86, plain, (![B_36]: (r2_hidden(B_36, '#skF_6') | ~m1_subset_1(B_36, '#skF_4') | ~m1_subset_1(B_36, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_78, c_44])).
% 23.30/13.69  tff(c_19030, plain, (v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_86])).
% 23.30/13.69  tff(c_21490, plain, (![A_928, B_929, C_930]: (r2_hidden('#skF_2'(A_928, B_929, C_930), B_929) | r2_hidden('#skF_2'(A_928, B_929, C_930), A_928) | r2_hidden('#skF_3'(A_928, B_929, C_930), C_930) | k2_xboole_0(A_928, B_929)=C_930)), inference(cnfTransformation, [status(thm)], [f_40])).
% 23.30/13.69  tff(c_20, plain, (![A_5, B_6, C_7]: (~r2_hidden('#skF_2'(A_5, B_6, C_7), C_7) | r2_hidden('#skF_3'(A_5, B_6, C_7), C_7) | k2_xboole_0(A_5, B_6)=C_7)), inference(cnfTransformation, [status(thm)], [f_40])).
% 23.30/13.69  tff(c_21712, plain, (![A_946, B_947]: (r2_hidden('#skF_2'(A_946, B_947, B_947), A_946) | r2_hidden('#skF_3'(A_946, B_947, B_947), B_947) | k2_xboole_0(A_946, B_947)=B_947)), inference(resolution, [status(thm)], [c_21490, c_20])).
% 23.30/13.69  tff(c_21047, plain, (![A_909, B_910, C_911]: (r2_hidden('#skF_2'(A_909, B_910, C_911), B_910) | r2_hidden('#skF_2'(A_909, B_910, C_911), A_909) | ~r2_hidden('#skF_3'(A_909, B_910, C_911), B_910) | k2_xboole_0(A_909, B_910)=C_911)), inference(cnfTransformation, [status(thm)], [f_40])).
% 23.30/13.69  tff(c_12, plain, (![A_5, B_6, C_7]: (~r2_hidden('#skF_2'(A_5, B_6, C_7), C_7) | ~r2_hidden('#skF_3'(A_5, B_6, C_7), B_6) | k2_xboole_0(A_5, B_6)=C_7)), inference(cnfTransformation, [status(thm)], [f_40])).
% 23.30/13.69  tff(c_21101, plain, (![A_909, B_910]: (r2_hidden('#skF_2'(A_909, B_910, B_910), A_909) | ~r2_hidden('#skF_3'(A_909, B_910, B_910), B_910) | k2_xboole_0(A_909, B_910)=B_910)), inference(resolution, [status(thm)], [c_21047, c_12])).
% 23.30/13.69  tff(c_21963, plain, (![A_950, B_951]: (r2_hidden('#skF_2'(A_950, B_951, B_951), A_950) | k2_xboole_0(A_950, B_951)=B_951)), inference(resolution, [status(thm)], [c_21712, c_21101])).
% 23.30/13.69  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 23.30/13.69  tff(c_22001, plain, (![A_952, B_953]: (~v1_xboole_0(A_952) | k2_xboole_0(A_952, B_953)=B_953)), inference(resolution, [status(thm)], [c_21963, c_2])).
% 23.30/13.69  tff(c_22015, plain, (![B_954]: (k2_xboole_0('#skF_5', B_954)=B_954)), inference(resolution, [status(thm)], [c_19030, c_22001])).
% 23.30/13.69  tff(c_28, plain, (![B_12]: (r1_tarski(B_12, B_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 23.30/13.69  tff(c_19034, plain, (![A_736, C_737, B_738]: (r1_tarski(A_736, C_737) | ~r1_tarski(k2_xboole_0(A_736, B_738), C_737))), inference(cnfTransformation, [status(thm)], [f_50])).
% 23.30/13.69  tff(c_19039, plain, (![A_736, B_738]: (r1_tarski(A_736, k2_xboole_0(A_736, B_738)))), inference(resolution, [status(thm)], [c_28, c_19034])).
% 23.30/13.69  tff(c_22062, plain, (![B_954]: (r1_tarski('#skF_5', B_954))), inference(superposition, [status(thm), theory('equality')], [c_22015, c_19039])).
% 23.30/13.69  tff(c_22094, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22062, c_42])).
% 23.30/13.69  tff(c_22096, plain, (~v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_86])).
% 23.30/13.69  tff(c_23039, plain, (![A_1075, B_1076, C_1077]: (r2_hidden('#skF_2'(A_1075, B_1076, C_1077), B_1076) | r2_hidden('#skF_2'(A_1075, B_1076, C_1077), A_1075) | r2_hidden('#skF_3'(A_1075, B_1076, C_1077), C_1077) | k2_xboole_0(A_1075, B_1076)=C_1077)), inference(cnfTransformation, [status(thm)], [f_40])).
% 23.30/13.69  tff(c_25588, plain, (![A_1152, B_1153]: (r2_hidden('#skF_2'(A_1152, B_1153, B_1153), A_1152) | r2_hidden('#skF_3'(A_1152, B_1153, B_1153), B_1153) | k2_xboole_0(A_1152, B_1153)=B_1153)), inference(resolution, [status(thm)], [c_23039, c_20])).
% 23.30/13.69  tff(c_23286, plain, (![A_1083, B_1084, C_1085]: (r2_hidden('#skF_2'(A_1083, B_1084, C_1085), B_1084) | r2_hidden('#skF_2'(A_1083, B_1084, C_1085), A_1083) | ~r2_hidden('#skF_3'(A_1083, B_1084, C_1085), B_1084) | k2_xboole_0(A_1083, B_1084)=C_1085)), inference(cnfTransformation, [status(thm)], [f_40])).
% 23.30/13.69  tff(c_23339, plain, (![A_1083, B_1084]: (r2_hidden('#skF_2'(A_1083, B_1084, B_1084), A_1083) | ~r2_hidden('#skF_3'(A_1083, B_1084, B_1084), B_1084) | k2_xboole_0(A_1083, B_1084)=B_1084)), inference(resolution, [status(thm)], [c_23286, c_12])).
% 23.30/13.69  tff(c_25658, plain, (![A_1154, B_1155]: (r2_hidden('#skF_2'(A_1154, B_1155, B_1155), A_1154) | k2_xboole_0(A_1154, B_1155)=B_1155)), inference(resolution, [status(thm)], [c_25588, c_23339])).
% 23.30/13.69  tff(c_32, plain, (![B_17, A_16]: (m1_subset_1(B_17, A_16) | ~r2_hidden(B_17, A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 23.30/13.69  tff(c_47921, plain, (![A_1755, B_1756]: (m1_subset_1('#skF_2'(A_1755, B_1756, B_1756), A_1755) | v1_xboole_0(A_1755) | k2_xboole_0(A_1755, B_1756)=B_1756)), inference(resolution, [status(thm)], [c_25658, c_32])).
% 23.30/13.69  tff(c_16327, plain, (![A_643, B_644, C_645]: (r2_hidden('#skF_2'(A_643, B_644, C_645), B_644) | r2_hidden('#skF_2'(A_643, B_644, C_645), A_643) | r2_hidden('#skF_3'(A_643, B_644, C_645), C_645) | k2_xboole_0(A_643, B_644)=C_645)), inference(cnfTransformation, [status(thm)], [f_40])).
% 23.30/13.69  tff(c_18179, plain, (![A_722, B_723]: (r2_hidden('#skF_2'(A_722, B_723, B_723), A_722) | r2_hidden('#skF_3'(A_722, B_723, B_723), B_723) | k2_xboole_0(A_722, B_723)=B_723)), inference(resolution, [status(thm)], [c_16327, c_20])).
% 23.30/13.69  tff(c_16678, plain, (![A_662, B_663, C_664]: (r2_hidden('#skF_2'(A_662, B_663, C_664), B_663) | r2_hidden('#skF_2'(A_662, B_663, C_664), A_662) | ~r2_hidden('#skF_3'(A_662, B_663, C_664), B_663) | k2_xboole_0(A_662, B_663)=C_664)), inference(cnfTransformation, [status(thm)], [f_40])).
% 23.30/13.69  tff(c_16731, plain, (![A_662, B_663]: (r2_hidden('#skF_2'(A_662, B_663, B_663), A_662) | ~r2_hidden('#skF_3'(A_662, B_663, B_663), B_663) | k2_xboole_0(A_662, B_663)=B_663)), inference(resolution, [status(thm)], [c_16678, c_12])).
% 23.30/13.69  tff(c_18574, plain, (![A_726, B_727]: (r2_hidden('#skF_2'(A_726, B_727, B_727), A_726) | k2_xboole_0(A_726, B_727)=B_727)), inference(resolution, [status(thm)], [c_18179, c_16731])).
% 23.30/13.69  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 23.30/13.69  tff(c_72, plain, (![D_35]: (r2_hidden(D_35, '#skF_6') | ~r2_hidden(D_35, '#skF_5') | ~m1_subset_1(D_35, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 23.30/13.69  tff(c_77, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_6') | ~m1_subset_1('#skF_1'('#skF_5'), '#skF_4') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_72])).
% 23.30/13.69  tff(c_128, plain, (~m1_subset_1('#skF_1'('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_77])).
% 23.30/13.69  tff(c_3351, plain, (![A_271, B_272, C_273]: (r2_hidden('#skF_2'(A_271, B_272, C_273), B_272) | r2_hidden('#skF_2'(A_271, B_272, C_273), A_271) | r2_hidden('#skF_3'(A_271, B_272, C_273), C_273) | k2_xboole_0(A_271, B_272)=C_273)), inference(cnfTransformation, [status(thm)], [f_40])).
% 23.30/13.69  tff(c_14487, plain, (![A_490, B_491]: (r2_hidden('#skF_2'(A_490, B_491, A_490), B_491) | r2_hidden('#skF_3'(A_490, B_491, A_490), A_490) | k2_xboole_0(A_490, B_491)=A_490)), inference(resolution, [status(thm)], [c_3351, c_20])).
% 23.30/13.69  tff(c_14545, plain, (![B_492]: (r2_hidden('#skF_3'(B_492, B_492, B_492), B_492) | k2_xboole_0(B_492, B_492)=B_492)), inference(resolution, [status(thm)], [c_14487, c_20])).
% 23.30/13.69  tff(c_14, plain, (![A_5, B_6, C_7]: (r2_hidden('#skF_2'(A_5, B_6, C_7), B_6) | r2_hidden('#skF_2'(A_5, B_6, C_7), A_5) | ~r2_hidden('#skF_3'(A_5, B_6, C_7), B_6) | k2_xboole_0(A_5, B_6)=C_7)), inference(cnfTransformation, [status(thm)], [f_40])).
% 23.30/13.69  tff(c_14315, plain, (![A_478, C_479]: (~r2_hidden('#skF_3'(A_478, A_478, C_479), A_478) | k2_xboole_0(A_478, A_478)=C_479 | r2_hidden('#skF_2'(A_478, A_478, C_479), A_478))), inference(factorization, [status(thm), theory('equality')], [c_14])).
% 23.30/13.69  tff(c_14342, plain, (![A_478]: (~r2_hidden('#skF_3'(A_478, A_478, A_478), A_478) | k2_xboole_0(A_478, A_478)=A_478)), inference(resolution, [status(thm)], [c_14315, c_12])).
% 23.30/13.69  tff(c_14567, plain, (![B_492]: (k2_xboole_0(B_492, B_492)=B_492)), inference(resolution, [status(thm)], [c_14545, c_14342])).
% 23.30/13.69  tff(c_3420, plain, (![A_271, B_272]: (r2_hidden('#skF_2'(A_271, B_272, B_272), A_271) | r2_hidden('#skF_3'(A_271, B_272, B_272), B_272) | k2_xboole_0(A_271, B_272)=B_272)), inference(resolution, [status(thm)], [c_3351, c_20])).
% 23.30/13.69  tff(c_4297, plain, (![A_297, B_298, C_299]: (r2_hidden('#skF_2'(A_297, B_298, C_299), B_298) | r2_hidden('#skF_2'(A_297, B_298, C_299), A_297) | ~r2_hidden('#skF_3'(A_297, B_298, C_299), B_298) | k2_xboole_0(A_297, B_298)=C_299)), inference(cnfTransformation, [status(thm)], [f_40])).
% 23.30/13.69  tff(c_9961, plain, (![A_385, B_386]: (r2_hidden('#skF_2'(A_385, B_386, B_386), A_385) | ~r2_hidden('#skF_3'(A_385, B_386, B_386), B_386) | k2_xboole_0(A_385, B_386)=B_386)), inference(resolution, [status(thm)], [c_4297, c_12])).
% 23.30/13.69  tff(c_13877, plain, (![A_468, B_469]: (r2_hidden('#skF_2'(A_468, B_469, B_469), A_468) | k2_xboole_0(A_468, B_469)=B_469)), inference(resolution, [status(thm)], [c_3420, c_9961])).
% 23.30/13.69  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 23.30/13.69  tff(c_22, plain, (![A_5, B_6, C_7]: (r2_hidden('#skF_2'(A_5, B_6, C_7), B_6) | r2_hidden('#skF_2'(A_5, B_6, C_7), A_5) | r2_hidden('#skF_3'(A_5, B_6, C_7), C_7) | k2_xboole_0(A_5, B_6)=C_7)), inference(cnfTransformation, [status(thm)], [f_40])).
% 23.30/13.69  tff(c_3990, plain, (![A_291, C_292]: (r2_hidden('#skF_3'(A_291, A_291, C_292), C_292) | k2_xboole_0(A_291, A_291)=C_292 | r2_hidden('#skF_2'(A_291, A_291, C_292), A_291))), inference(factorization, [status(thm), theory('equality')], [c_22])).
% 23.30/13.69  tff(c_4046, plain, (![A_293]: (r2_hidden('#skF_3'(A_293, A_293, A_293), A_293) | k2_xboole_0(A_293, A_293)=A_293)), inference(resolution, [status(thm)], [c_3990, c_20])).
% 23.30/13.69  tff(c_3848, plain, (![A_286, C_287]: (~r2_hidden('#skF_3'(A_286, A_286, C_287), A_286) | k2_xboole_0(A_286, A_286)=C_287 | r2_hidden('#skF_2'(A_286, A_286, C_287), A_286))), inference(factorization, [status(thm), theory('equality')], [c_14])).
% 23.30/13.69  tff(c_3876, plain, (![A_286]: (~r2_hidden('#skF_3'(A_286, A_286, A_286), A_286) | k2_xboole_0(A_286, A_286)=A_286)), inference(resolution, [status(thm)], [c_3848, c_12])).
% 23.30/13.69  tff(c_4068, plain, (![A_293]: (k2_xboole_0(A_293, A_293)=A_293)), inference(resolution, [status(thm)], [c_4046, c_3876])).
% 23.30/13.69  tff(c_36, plain, (![B_17, A_16]: (m1_subset_1(B_17, A_16) | ~v1_xboole_0(B_17) | ~v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 23.30/13.69  tff(c_132, plain, (~v1_xboole_0('#skF_1'('#skF_5')) | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_128])).
% 23.30/13.69  tff(c_133, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_132])).
% 23.30/13.69  tff(c_141, plain, (![C_58, A_59, B_60]: (r2_hidden(C_58, A_59) | ~r2_hidden(C_58, B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 23.30/13.69  tff(c_183, plain, (![A_72, A_73]: (r2_hidden('#skF_1'(A_72), A_73) | ~m1_subset_1(A_72, k1_zfmisc_1(A_73)) | v1_xboole_0(A_72))), inference(resolution, [status(thm)], [c_4, c_141])).
% 23.30/13.69  tff(c_197, plain, (![A_72, A_73]: (m1_subset_1('#skF_1'(A_72), A_73) | v1_xboole_0(A_73) | ~m1_subset_1(A_72, k1_zfmisc_1(A_73)) | v1_xboole_0(A_72))), inference(resolution, [status(thm)], [c_183, c_32])).
% 23.30/13.69  tff(c_221, plain, (![D_77, B_78, A_79]: (r2_hidden(D_77, B_78) | r2_hidden(D_77, A_79) | ~r2_hidden(D_77, k2_xboole_0(A_79, B_78)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 23.30/13.69  tff(c_244, plain, (![A_79, B_78]: (r2_hidden('#skF_1'(k2_xboole_0(A_79, B_78)), B_78) | r2_hidden('#skF_1'(k2_xboole_0(A_79, B_78)), A_79) | v1_xboole_0(k2_xboole_0(A_79, B_78)))), inference(resolution, [status(thm)], [c_4, c_221])).
% 23.30/13.69  tff(c_3513, plain, (![B_278]: (v1_xboole_0(k2_xboole_0(B_278, B_278)) | r2_hidden('#skF_1'(k2_xboole_0(B_278, B_278)), B_278))), inference(factorization, [status(thm), theory('equality')], [c_244])).
% 23.30/13.69  tff(c_3533, plain, (r2_hidden('#skF_1'(k2_xboole_0('#skF_5', '#skF_5')), '#skF_6') | ~m1_subset_1('#skF_1'(k2_xboole_0('#skF_5', '#skF_5')), '#skF_4') | v1_xboole_0(k2_xboole_0('#skF_5', '#skF_5'))), inference(resolution, [status(thm)], [c_3513, c_44])).
% 23.30/13.69  tff(c_3535, plain, (~m1_subset_1('#skF_1'(k2_xboole_0('#skF_5', '#skF_5')), '#skF_4')), inference(splitLeft, [status(thm)], [c_3533])).
% 23.30/13.69  tff(c_3551, plain, (v1_xboole_0('#skF_4') | ~m1_subset_1(k2_xboole_0('#skF_5', '#skF_5'), k1_zfmisc_1('#skF_4')) | v1_xboole_0(k2_xboole_0('#skF_5', '#skF_5'))), inference(resolution, [status(thm)], [c_197, c_3535])).
% 23.30/13.69  tff(c_3559, plain, (~m1_subset_1(k2_xboole_0('#skF_5', '#skF_5'), k1_zfmisc_1('#skF_4')) | v1_xboole_0(k2_xboole_0('#skF_5', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_133, c_3551])).
% 23.30/13.69  tff(c_3561, plain, (~m1_subset_1(k2_xboole_0('#skF_5', '#skF_5'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_3559])).
% 23.30/13.69  tff(c_4082, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4068, c_3561])).
% 23.30/13.69  tff(c_4089, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_4082])).
% 23.30/13.69  tff(c_4090, plain, (v1_xboole_0(k2_xboole_0('#skF_5', '#skF_5'))), inference(splitRight, [status(thm)], [c_3559])).
% 23.30/13.69  tff(c_119, plain, (![D_49, B_50, A_51]: (~r2_hidden(D_49, B_50) | r2_hidden(D_49, k2_xboole_0(A_51, B_50)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 23.30/13.69  tff(c_127, plain, (![A_51, B_50, D_49]: (~v1_xboole_0(k2_xboole_0(A_51, B_50)) | ~r2_hidden(D_49, B_50))), inference(resolution, [status(thm)], [c_119, c_2])).
% 23.30/13.69  tff(c_4096, plain, (![D_49]: (~r2_hidden(D_49, '#skF_5'))), inference(resolution, [status(thm)], [c_4090, c_127])).
% 23.30/13.69  tff(c_13968, plain, (![B_470]: (k2_xboole_0('#skF_5', B_470)=B_470)), inference(resolution, [status(thm)], [c_13877, c_4096])).
% 23.30/13.69  tff(c_135, plain, (![A_55, C_56, B_57]: (r1_tarski(A_55, C_56) | ~r1_tarski(k2_xboole_0(A_55, B_57), C_56))), inference(cnfTransformation, [status(thm)], [f_50])).
% 23.30/13.69  tff(c_140, plain, (![A_55, B_57]: (r1_tarski(A_55, k2_xboole_0(A_55, B_57)))), inference(resolution, [status(thm)], [c_28, c_135])).
% 23.30/13.69  tff(c_14078, plain, (![B_470]: (r1_tarski('#skF_5', B_470))), inference(superposition, [status(thm), theory('equality')], [c_13968, c_140])).
% 23.30/13.69  tff(c_14135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14078, c_42])).
% 23.30/13.69  tff(c_14137, plain, (m1_subset_1('#skF_1'(k2_xboole_0('#skF_5', '#skF_5')), '#skF_4')), inference(splitRight, [status(thm)], [c_3533])).
% 23.30/13.69  tff(c_14581, plain, (m1_subset_1('#skF_1'('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14567, c_14137])).
% 23.30/13.69  tff(c_14585, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128, c_14581])).
% 23.30/13.69  tff(c_14587, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_132])).
% 23.30/13.69  tff(c_14637, plain, (![D_513, B_514, A_515]: (r2_hidden(D_513, B_514) | r2_hidden(D_513, A_515) | ~r2_hidden(D_513, k2_xboole_0(A_515, B_514)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 23.30/13.69  tff(c_14655, plain, (![A_515, B_514]: (r2_hidden('#skF_1'(k2_xboole_0(A_515, B_514)), B_514) | r2_hidden('#skF_1'(k2_xboole_0(A_515, B_514)), A_515) | v1_xboole_0(k2_xboole_0(A_515, B_514)))), inference(resolution, [status(thm)], [c_4, c_14637])).
% 23.30/13.69  tff(c_16747, plain, (![B_665]: (v1_xboole_0(k2_xboole_0(B_665, B_665)) | r2_hidden('#skF_1'(k2_xboole_0(B_665, B_665)), B_665))), inference(factorization, [status(thm), theory('equality')], [c_14655])).
% 23.30/13.69  tff(c_40, plain, (![C_21, A_18, B_19]: (r2_hidden(C_21, A_18) | ~r2_hidden(C_21, B_19) | ~m1_subset_1(B_19, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 23.30/13.69  tff(c_17361, plain, (![B_696, A_697]: (r2_hidden('#skF_1'(k2_xboole_0(B_696, B_696)), A_697) | ~m1_subset_1(B_696, k1_zfmisc_1(A_697)) | v1_xboole_0(k2_xboole_0(B_696, B_696)))), inference(resolution, [status(thm)], [c_16747, c_40])).
% 23.30/13.69  tff(c_17383, plain, (![A_698, B_699]: (~v1_xboole_0(A_698) | ~m1_subset_1(B_699, k1_zfmisc_1(A_698)) | v1_xboole_0(k2_xboole_0(B_699, B_699)))), inference(resolution, [status(thm)], [c_17361, c_2])).
% 23.30/13.69  tff(c_17406, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0(k2_xboole_0('#skF_5', '#skF_5'))), inference(resolution, [status(thm)], [c_48, c_17383])).
% 23.30/13.69  tff(c_17418, plain, (v1_xboole_0(k2_xboole_0('#skF_5', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_14587, c_17406])).
% 23.30/13.69  tff(c_17426, plain, (![D_49]: (~r2_hidden(D_49, '#skF_5'))), inference(resolution, [status(thm)], [c_17418, c_127])).
% 23.30/13.69  tff(c_18866, plain, (![B_732]: (k2_xboole_0('#skF_5', B_732)=B_732)), inference(resolution, [status(thm)], [c_18574, c_17426])).
% 23.30/13.69  tff(c_14590, plain, (![A_496, C_497, B_498]: (r1_tarski(A_496, C_497) | ~r1_tarski(k2_xboole_0(A_496, B_498), C_497))), inference(cnfTransformation, [status(thm)], [f_50])).
% 23.30/13.69  tff(c_14595, plain, (![A_496, B_498]: (r1_tarski(A_496, k2_xboole_0(A_496, B_498)))), inference(resolution, [status(thm)], [c_28, c_14590])).
% 23.30/13.69  tff(c_18961, plain, (![B_732]: (r1_tarski('#skF_5', B_732))), inference(superposition, [status(thm), theory('equality')], [c_18866, c_14595])).
% 23.30/13.69  tff(c_19023, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18961, c_42])).
% 23.30/13.69  tff(c_19025, plain, (m1_subset_1('#skF_1'('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_77])).
% 23.30/13.69  tff(c_38, plain, (![B_17, A_16]: (v1_xboole_0(B_17) | ~m1_subset_1(B_17, A_16) | ~v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 23.30/13.69  tff(c_19029, plain, (v1_xboole_0('#skF_1'('#skF_5')) | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_19025, c_38])).
% 23.30/13.69  tff(c_22112, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_19029])).
% 23.30/13.69  tff(c_34, plain, (![B_17, A_16]: (r2_hidden(B_17, A_16) | ~m1_subset_1(B_17, A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 23.30/13.69  tff(c_22148, plain, (![C_967, A_968, B_969]: (r2_hidden(C_967, A_968) | ~r2_hidden(C_967, B_969) | ~m1_subset_1(B_969, k1_zfmisc_1(A_968)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 23.30/13.69  tff(c_22365, plain, (![B_1008, A_1009, A_1010]: (r2_hidden(B_1008, A_1009) | ~m1_subset_1(A_1010, k1_zfmisc_1(A_1009)) | ~m1_subset_1(B_1008, A_1010) | v1_xboole_0(A_1010))), inference(resolution, [status(thm)], [c_34, c_22148])).
% 23.30/13.69  tff(c_22376, plain, (![B_1008]: (r2_hidden(B_1008, '#skF_4') | ~m1_subset_1(B_1008, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_48, c_22365])).
% 23.30/13.69  tff(c_22388, plain, (![B_1011]: (r2_hidden(B_1011, '#skF_4') | ~m1_subset_1(B_1011, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_22096, c_22376])).
% 23.30/13.69  tff(c_22393, plain, (![B_1011]: (m1_subset_1(B_1011, '#skF_4') | v1_xboole_0('#skF_4') | ~m1_subset_1(B_1011, '#skF_5'))), inference(resolution, [status(thm)], [c_22388, c_32])).
% 23.30/13.69  tff(c_22400, plain, (![B_1011]: (m1_subset_1(B_1011, '#skF_4') | ~m1_subset_1(B_1011, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_22112, c_22393])).
% 23.30/13.69  tff(c_47963, plain, (![B_1756]: (m1_subset_1('#skF_2'('#skF_5', B_1756, B_1756), '#skF_4') | v1_xboole_0('#skF_5') | k2_xboole_0('#skF_5', B_1756)=B_1756)), inference(resolution, [status(thm)], [c_47921, c_22400])).
% 23.30/13.69  tff(c_47996, plain, (![B_1756]: (m1_subset_1('#skF_2'('#skF_5', B_1756, B_1756), '#skF_4') | k2_xboole_0('#skF_5', B_1756)=B_1756)), inference(negUnitSimplification, [status(thm)], [c_22096, c_47963])).
% 23.30/13.69  tff(c_25699, plain, (![B_1155]: (r2_hidden('#skF_2'('#skF_5', B_1155, B_1155), '#skF_6') | ~m1_subset_1('#skF_2'('#skF_5', B_1155, B_1155), '#skF_4') | k2_xboole_0('#skF_5', B_1155)=B_1155)), inference(resolution, [status(thm)], [c_25658, c_44])).
% 23.30/13.69  tff(c_23585, plain, (![A_1100, B_1101]: (r2_hidden('#skF_2'(A_1100, B_1101, A_1100), B_1101) | r2_hidden('#skF_3'(A_1100, B_1101, A_1100), A_1100) | k2_xboole_0(A_1100, B_1101)=A_1100)), inference(resolution, [status(thm)], [c_23039, c_20])).
% 23.30/13.69  tff(c_23695, plain, (![B_1104]: (r2_hidden('#skF_3'(B_1104, B_1104, B_1104), B_1104) | k2_xboole_0(B_1104, B_1104)=B_1104)), inference(resolution, [status(thm)], [c_23585, c_20])).
% 23.30/13.69  tff(c_23416, plain, (![A_1094, C_1095]: (~r2_hidden('#skF_3'(A_1094, A_1094, C_1095), A_1094) | k2_xboole_0(A_1094, A_1094)=C_1095 | r2_hidden('#skF_2'(A_1094, A_1094, C_1095), A_1094))), inference(factorization, [status(thm), theory('equality')], [c_14])).
% 23.30/13.69  tff(c_23443, plain, (![A_1094]: (~r2_hidden('#skF_3'(A_1094, A_1094, A_1094), A_1094) | k2_xboole_0(A_1094, A_1094)=A_1094)), inference(resolution, [status(thm)], [c_23416, c_12])).
% 23.30/13.69  tff(c_23715, plain, (![B_1104]: (k2_xboole_0(B_1104, B_1104)=B_1104)), inference(resolution, [status(thm)], [c_23695, c_23443])).
% 23.30/13.69  tff(c_10, plain, (![D_10, A_5, B_6]: (~r2_hidden(D_10, A_5) | r2_hidden(D_10, k2_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 23.30/13.69  tff(c_22402, plain, (![A_1012, B_1013, C_1014]: (~r2_hidden('#skF_2'(A_1012, B_1013, C_1014), C_1014) | r2_hidden('#skF_3'(A_1012, B_1013, C_1014), C_1014) | k2_xboole_0(A_1012, B_1013)=C_1014)), inference(cnfTransformation, [status(thm)], [f_40])).
% 23.30/13.69  tff(c_56158, plain, (![A_1925, B_1926, A_1927, B_1928]: (r2_hidden('#skF_3'(A_1925, B_1926, k2_xboole_0(A_1927, B_1928)), k2_xboole_0(A_1927, B_1928)) | k2_xboole_0(A_1927, B_1928)=k2_xboole_0(A_1925, B_1926) | ~r2_hidden('#skF_2'(A_1925, B_1926, k2_xboole_0(A_1927, B_1928)), A_1927))), inference(resolution, [status(thm)], [c_10, c_22402])).
% 23.30/13.69  tff(c_22621, plain, (![A_1039, B_1040, C_1041]: (~r2_hidden('#skF_2'(A_1039, B_1040, C_1041), C_1041) | ~r2_hidden('#skF_3'(A_1039, B_1040, C_1041), B_1040) | k2_xboole_0(A_1039, B_1040)=C_1041)), inference(cnfTransformation, [status(thm)], [f_40])).
% 23.30/13.69  tff(c_22644, plain, (![A_1039, B_1040, A_5, B_6]: (~r2_hidden('#skF_3'(A_1039, B_1040, k2_xboole_0(A_5, B_6)), B_1040) | k2_xboole_0(A_5, B_6)=k2_xboole_0(A_1039, B_1040) | ~r2_hidden('#skF_2'(A_1039, B_1040, k2_xboole_0(A_5, B_6)), A_5))), inference(resolution, [status(thm)], [c_10, c_22621])).
% 23.30/13.70  tff(c_73770, plain, (![A_2220, A_2221, B_2222]: (k2_xboole_0(A_2220, k2_xboole_0(A_2221, B_2222))=k2_xboole_0(A_2221, B_2222) | ~r2_hidden('#skF_2'(A_2220, k2_xboole_0(A_2221, B_2222), k2_xboole_0(A_2221, B_2222)), A_2221))), inference(resolution, [status(thm)], [c_56158, c_22644])).
% 23.30/13.70  tff(c_74016, plain, (![A_2220, B_1104]: (k2_xboole_0(A_2220, k2_xboole_0(B_1104, B_1104))=k2_xboole_0(B_1104, B_1104) | ~r2_hidden('#skF_2'(A_2220, k2_xboole_0(B_1104, B_1104), B_1104), B_1104))), inference(superposition, [status(thm), theory('equality')], [c_23715, c_73770])).
% 23.30/13.70  tff(c_81117, plain, (![A_2281, B_2282]: (k2_xboole_0(A_2281, B_2282)=B_2282 | ~r2_hidden('#skF_2'(A_2281, B_2282, B_2282), B_2282))), inference(demodulation, [status(thm), theory('equality')], [c_23715, c_23715, c_23715, c_74016])).
% 23.30/13.70  tff(c_81628, plain, (~m1_subset_1('#skF_2'('#skF_5', '#skF_6', '#skF_6'), '#skF_4') | k2_xboole_0('#skF_5', '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_25699, c_81117])).
% 23.30/13.70  tff(c_82347, plain, (~m1_subset_1('#skF_2'('#skF_5', '#skF_6', '#skF_6'), '#skF_4')), inference(splitLeft, [status(thm)], [c_81628])).
% 23.30/13.70  tff(c_82354, plain, (k2_xboole_0('#skF_5', '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_47996, c_82347])).
% 23.30/13.70  tff(c_22097, plain, (![A_955, C_956, B_957]: (r1_tarski(A_955, C_956) | ~r1_tarski(k2_xboole_0(A_955, B_957), C_956))), inference(cnfTransformation, [status(thm)], [f_50])).
% 23.30/13.70  tff(c_22102, plain, (![A_955, B_957]: (r1_tarski(A_955, k2_xboole_0(A_955, B_957)))), inference(resolution, [status(thm)], [c_28, c_22097])).
% 23.30/13.70  tff(c_82847, plain, (r1_tarski('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_82354, c_22102])).
% 23.30/13.70  tff(c_82954, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_82847])).
% 23.30/13.70  tff(c_82955, plain, (k2_xboole_0('#skF_5', '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_81628])).
% 23.30/13.70  tff(c_83260, plain, (r1_tarski('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_82955, c_22102])).
% 23.30/13.70  tff(c_83367, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_83260])).
% 23.30/13.70  tff(c_83369, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_19029])).
% 23.30/13.70  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 23.30/13.70  tff(c_19024, plain, (v1_xboole_0('#skF_5') | r2_hidden('#skF_1'('#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_77])).
% 23.30/13.70  tff(c_83370, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_22096, c_19024])).
% 23.30/13.70  tff(c_83395, plain, (![C_2295, A_2296, B_2297]: (r2_hidden(C_2295, A_2296) | ~r2_hidden(C_2295, B_2297) | ~m1_subset_1(B_2297, k1_zfmisc_1(A_2296)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 23.30/13.70  tff(c_83411, plain, (![A_2298]: (r2_hidden('#skF_1'('#skF_5'), A_2298) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_2298)))), inference(resolution, [status(thm)], [c_83370, c_83395])).
% 23.30/13.70  tff(c_83430, plain, (![A_2299]: (~v1_xboole_0(A_2299) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_2299)))), inference(resolution, [status(thm)], [c_83411, c_2])).
% 23.30/13.70  tff(c_83436, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_46, c_83430])).
% 23.30/13.70  tff(c_83441, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83369, c_83436])).
% 23.30/13.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.30/13.70  
% 23.30/13.70  Inference rules
% 23.30/13.70  ----------------------
% 23.30/13.70  #Ref     : 0
% 23.30/13.70  #Sup     : 17872
% 23.30/13.70  #Fact    : 246
% 23.30/13.70  #Define  : 0
% 23.30/13.70  #Split   : 140
% 23.30/13.70  #Chain   : 0
% 23.30/13.70  #Close   : 0
% 23.30/13.70  
% 23.30/13.70  Ordering : KBO
% 23.30/13.70  
% 23.30/13.70  Simplification rules
% 23.30/13.70  ----------------------
% 23.30/13.70  #Subsume      : 7492
% 23.30/13.70  #Demod        : 9773
% 23.30/13.70  #Tautology    : 3357
% 23.30/13.70  #SimpNegUnit  : 2069
% 23.30/13.70  #BackRed      : 1244
% 23.30/13.70  
% 23.30/13.70  #Partial instantiations: 0
% 23.30/13.70  #Strategies tried      : 1
% 23.30/13.70  
% 23.30/13.70  Timing (in seconds)
% 23.30/13.70  ----------------------
% 23.30/13.70  Preprocessing        : 0.31
% 23.30/13.70  Parsing              : 0.17
% 23.30/13.70  CNF conversion       : 0.02
% 23.30/13.70  Main loop            : 12.55
% 23.30/13.70  Inferencing          : 2.51
% 23.30/13.70  Reduction            : 3.66
% 23.30/13.70  Demodulation         : 2.59
% 23.30/13.70  BG Simplification    : 0.23
% 23.30/13.70  Subsumption          : 5.48
% 23.30/13.70  Abstraction          : 0.36
% 23.30/13.70  MUC search           : 0.00
% 23.30/13.70  Cooper               : 0.00
% 23.30/13.70  Total                : 12.91
% 23.30/13.70  Index Insertion      : 0.00
% 23.30/13.70  Index Deletion       : 0.00
% 23.30/13.70  Index Matching       : 0.00
% 23.30/13.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
