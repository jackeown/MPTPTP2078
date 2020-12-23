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
% DateTime   : Thu Dec  3 10:10:11 EST 2020

% Result     : Theorem 5.98s
% Output     : CNFRefutation 6.27s
% Verified   : 
% Statistics : Number of formulae       :  251 ( 917 expanded)
%              Number of leaves         :   38 ( 314 expanded)
%              Depth                    :   13
%              Number of atoms          :  389 (2210 expanded)
%              Number of equality atoms :   79 ( 341 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_50,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_mcart_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_64,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

tff(c_18,plain,(
    ! [A_15] : r1_tarski(k1_xboole_0,A_15) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3733,plain,(
    ! [A_674,C_675,B_676] :
      ( r1_xboole_0(A_674,C_675)
      | ~ r1_tarski(A_674,k4_xboole_0(B_676,C_675)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_3759,plain,(
    ! [C_677] : r1_xboole_0(k1_xboole_0,C_677) ),
    inference(resolution,[status(thm)],[c_18,c_3733])).

tff(c_20,plain,(
    ! [B_17,A_16] :
      ( ~ r1_xboole_0(B_17,A_16)
      | ~ r1_tarski(B_17,A_16)
      | v1_xboole_0(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3762,plain,(
    ! [C_677] :
      ( ~ r1_tarski(k1_xboole_0,C_677)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_3759,c_20])).

tff(c_3767,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_3762])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3709,plain,(
    ! [A_666,B_667] :
      ( ~ r2_hidden('#skF_2'(A_666,B_667),B_667)
      | r1_tarski(A_666,B_667) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3714,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_3709])).

tff(c_2488,plain,(
    ! [A_461,C_462,B_463] :
      ( r1_xboole_0(A_461,C_462)
      | ~ r1_tarski(A_461,k4_xboole_0(B_463,C_462)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2509,plain,(
    ! [C_464] : r1_xboole_0(k1_xboole_0,C_464) ),
    inference(resolution,[status(thm)],[c_18,c_2488])).

tff(c_2512,plain,(
    ! [C_464] :
      ( ~ r1_tarski(k1_xboole_0,C_464)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2509,c_20])).

tff(c_2517,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2512])).

tff(c_44,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2432,plain,(
    ! [A_443,B_444] :
      ( r1_tarski(A_443,B_444)
      | ~ m1_subset_1(A_443,k1_zfmisc_1(B_444)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2442,plain,(
    r1_tarski('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_2432])).

tff(c_46,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2443,plain,(
    r1_tarski('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_2432])).

tff(c_2458,plain,(
    ! [A_452,B_453] :
      ( r2_hidden('#skF_2'(A_452,B_453),A_452)
      | r1_tarski(A_452,B_453) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2462,plain,(
    ! [A_452,B_453] :
      ( ~ v1_xboole_0(A_452)
      | r1_tarski(A_452,B_453) ) ),
    inference(resolution,[status(thm)],[c_2458,c_2])).

tff(c_2545,plain,(
    ! [A_471,C_472] :
      ( r1_xboole_0(A_471,C_472)
      | ~ v1_xboole_0(A_471) ) ),
    inference(resolution,[status(thm)],[c_2462,c_2488])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( r1_xboole_0(B_11,A_10)
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2603,plain,(
    ! [C_480,A_481] :
      ( r1_xboole_0(C_480,A_481)
      | ~ v1_xboole_0(A_481) ) ),
    inference(resolution,[status(thm)],[c_2545,c_12])).

tff(c_2670,plain,(
    ! [C_498,A_499] :
      ( ~ r1_tarski(C_498,A_499)
      | v1_xboole_0(C_498)
      | ~ v1_xboole_0(A_499) ) ),
    inference(resolution,[status(thm)],[c_2603,c_20])).

tff(c_2702,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_2443,c_2670])).

tff(c_2717,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2702])).

tff(c_40,plain,(
    r2_hidden('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2586,plain,(
    ! [A_477,B_478,C_479] : k2_zfmisc_1(k2_zfmisc_1(A_477,B_478),C_479) = k3_zfmisc_1(A_477,B_478,C_479) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_28,plain,(
    ! [A_23,C_25,B_24] :
      ( r2_hidden(k2_mcart_1(A_23),C_25)
      | ~ r2_hidden(A_23,k2_zfmisc_1(B_24,C_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2848,plain,(
    ! [A_545,C_546,A_547,B_548] :
      ( r2_hidden(k2_mcart_1(A_545),C_546)
      | ~ r2_hidden(A_545,k3_zfmisc_1(A_547,B_548,C_546)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2586,c_28])).

tff(c_2862,plain,(
    r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_40,c_2848])).

tff(c_94,plain,(
    ! [A_61,C_62,B_63] :
      ( r1_xboole_0(A_61,C_62)
      | ~ r1_tarski(A_61,k4_xboole_0(B_63,C_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_110,plain,(
    ! [C_64] : r1_xboole_0(k1_xboole_0,C_64) ),
    inference(resolution,[status(thm)],[c_18,c_94])).

tff(c_113,plain,(
    ! [C_64] :
      ( ~ r1_tarski(k1_xboole_0,C_64)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_110,c_20])).

tff(c_118,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_113])).

tff(c_87,plain,(
    ! [A_58,B_59] :
      ( ~ r2_hidden('#skF_2'(A_58,B_59),B_59)
      | r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_92,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_87])).

tff(c_38,plain,
    ( ~ r2_hidden(k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_8')
    | ~ r2_hidden(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_7')
    | ~ r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_60,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_63,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(A_50,B_51)
      | ~ m1_subset_1(A_50,k1_zfmisc_1(B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_78,plain,(
    r1_tarski('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_63])).

tff(c_80,plain,(
    ! [A_52,B_53] :
      ( r2_hidden('#skF_2'(A_52,B_53),A_52)
      | r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_84,plain,(
    ! [A_52,B_53] :
      ( ~ v1_xboole_0(A_52)
      | r1_tarski(A_52,B_53) ) ),
    inference(resolution,[status(thm)],[c_80,c_2])).

tff(c_157,plain,(
    ! [A_71,C_72] :
      ( r1_xboole_0(A_71,C_72)
      | ~ v1_xboole_0(A_71) ) ),
    inference(resolution,[status(thm)],[c_84,c_94])).

tff(c_188,plain,(
    ! [C_78,A_79] :
      ( r1_xboole_0(C_78,A_79)
      | ~ v1_xboole_0(A_79) ) ),
    inference(resolution,[status(thm)],[c_157,c_12])).

tff(c_288,plain,(
    ! [C_100,A_101] :
      ( ~ r1_tarski(C_100,A_101)
      | v1_xboole_0(C_100)
      | ~ v1_xboole_0(A_101) ) ),
    inference(resolution,[status(thm)],[c_188,c_20])).

tff(c_317,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_288])).

tff(c_322,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_317])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_79,plain,(
    r1_tarski('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_63])).

tff(c_318,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_79,c_288])).

tff(c_323,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_318])).

tff(c_42,plain,(
    m1_subset_1('#skF_9',k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_390,plain,(
    ! [A_118,B_119,C_120,D_121] :
      ( k7_mcart_1(A_118,B_119,C_120,D_121) = k2_mcart_1(D_121)
      | ~ m1_subset_1(D_121,k3_zfmisc_1(A_118,B_119,C_120))
      | k1_xboole_0 = C_120
      | k1_xboole_0 = B_119
      | k1_xboole_0 = A_118 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_394,plain,
    ( k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_42,c_390])).

tff(c_422,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_394])).

tff(c_428,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_118])).

tff(c_432,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_323,c_428])).

tff(c_434,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_394])).

tff(c_568,plain,(
    ! [A_158,B_159,C_160,D_161] :
      ( k5_mcart_1(A_158,B_159,C_160,D_161) = k1_mcart_1(k1_mcart_1(D_161))
      | ~ m1_subset_1(D_161,k3_zfmisc_1(A_158,B_159,C_160))
      | k1_xboole_0 = C_160
      | k1_xboole_0 = B_159
      | k1_xboole_0 = A_158 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_571,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_42,c_568])).

tff(c_574,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_434,c_571])).

tff(c_880,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_574])).

tff(c_892,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_880,c_118])).

tff(c_896,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_322,c_892])).

tff(c_897,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') ),
    inference(splitRight,[status(thm)],[c_574])).

tff(c_943,plain,(
    k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_897])).

tff(c_26,plain,(
    ! [A_20,B_21,C_22] : k2_zfmisc_1(k2_zfmisc_1(A_20,B_21),C_22) = k3_zfmisc_1(A_20,B_21,C_22) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_229,plain,(
    ! [A_84,B_85,C_86] :
      ( r2_hidden(k1_mcart_1(A_84),B_85)
      | ~ r2_hidden(A_84,k2_zfmisc_1(B_85,C_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1147,plain,(
    ! [A_248,A_249,B_250,C_251] :
      ( r2_hidden(k1_mcart_1(A_248),k2_zfmisc_1(A_249,B_250))
      | ~ r2_hidden(A_248,k3_zfmisc_1(A_249,B_250,C_251)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_229])).

tff(c_1184,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_40,c_1147])).

tff(c_30,plain,(
    ! [A_23,B_24,C_25] :
      ( r2_hidden(k1_mcart_1(A_23),B_24)
      | ~ r2_hidden(A_23,k2_zfmisc_1(B_24,C_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1191,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_1184,c_30])).

tff(c_1199,plain,(
    r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_943,c_1191])).

tff(c_1201,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1199])).

tff(c_1202,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_897])).

tff(c_77,plain,(
    r1_tarski('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_63])).

tff(c_265,plain,(
    ! [A_95,C_96,B_97] :
      ( r2_hidden(k2_mcart_1(A_95),C_96)
      | ~ r2_hidden(A_95,k2_zfmisc_1(B_97,C_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_473,plain,(
    ! [A_150,C_151,A_152,B_153] :
      ( r2_hidden(k2_mcart_1(A_150),C_151)
      | ~ r2_hidden(A_150,k3_zfmisc_1(A_152,B_153,C_151)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_265])).

tff(c_487,plain,(
    r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_40,c_473])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_496,plain,(
    ! [B_154] :
      ( r2_hidden(k2_mcart_1('#skF_9'),B_154)
      | ~ r1_tarski('#skF_8',B_154) ) ),
    inference(resolution,[status(thm)],[c_487,c_6])).

tff(c_531,plain,(
    ! [B_156,B_157] :
      ( r2_hidden(k2_mcart_1('#skF_9'),B_156)
      | ~ r1_tarski(B_157,B_156)
      | ~ r1_tarski('#skF_8',B_157) ) ),
    inference(resolution,[status(thm)],[c_496,c_6])).

tff(c_547,plain,
    ( r2_hidden(k2_mcart_1('#skF_9'),'#skF_5')
    | ~ r1_tarski('#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_77,c_531])).

tff(c_559,plain,(
    r2_hidden(k2_mcart_1('#skF_9'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_547])).

tff(c_590,plain,(
    ! [B_162] :
      ( r2_hidden(k2_mcart_1('#skF_9'),B_162)
      | ~ r1_tarski('#skF_5',B_162) ) ),
    inference(resolution,[status(thm)],[c_559,c_6])).

tff(c_679,plain,(
    ! [B_181,B_182] :
      ( r2_hidden(k2_mcart_1('#skF_9'),B_181)
      | ~ r1_tarski(B_182,B_181)
      | ~ r1_tarski('#skF_5',B_182) ) ),
    inference(resolution,[status(thm)],[c_590,c_6])).

tff(c_707,plain,(
    ! [A_15] :
      ( r2_hidden(k2_mcart_1('#skF_9'),A_15)
      | ~ r1_tarski('#skF_5',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_679])).

tff(c_738,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_707])).

tff(c_1205,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1202,c_738])).

tff(c_1221,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_1205])).

tff(c_1223,plain,(
    r1_tarski('#skF_5',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_707])).

tff(c_609,plain,(
    ! [B_162] :
      ( ~ v1_xboole_0(B_162)
      | ~ r1_tarski('#skF_5',B_162) ) ),
    inference(resolution,[status(thm)],[c_590,c_2])).

tff(c_1228,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1223,c_609])).

tff(c_1243,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_1228])).

tff(c_1244,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_318])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1601,plain,(
    ! [B_326,C_327] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_326,C_327))),B_326)
      | v1_xboole_0(k2_zfmisc_1(B_326,C_327)) ) ),
    inference(resolution,[status(thm)],[c_4,c_229])).

tff(c_1625,plain,(
    ! [B_326,C_327] :
      ( ~ v1_xboole_0(B_326)
      | v1_xboole_0(k2_zfmisc_1(B_326,C_327)) ) ),
    inference(resolution,[status(thm)],[c_1601,c_2])).

tff(c_1631,plain,(
    ! [B_328,C_329] :
      ( ~ v1_xboole_0(B_328)
      | v1_xboole_0(k2_zfmisc_1(B_328,C_329)) ) ),
    inference(resolution,[status(thm)],[c_1601,c_2])).

tff(c_1676,plain,(
    ! [A_332,B_333,C_334] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_332,B_333))
      | v1_xboole_0(k3_zfmisc_1(A_332,B_333,C_334)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1631])).

tff(c_59,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_40,c_2])).

tff(c_1680,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_1676,c_59])).

tff(c_1707,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1625,c_1680])).

tff(c_1711,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1244,c_1707])).

tff(c_1712,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_317])).

tff(c_2136,plain,(
    ! [B_409,C_410] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_409,C_410))),C_410)
      | v1_xboole_0(k2_zfmisc_1(B_409,C_410)) ) ),
    inference(resolution,[status(thm)],[c_4,c_265])).

tff(c_2158,plain,(
    ! [C_410,B_409] :
      ( ~ v1_xboole_0(C_410)
      | v1_xboole_0(k2_zfmisc_1(B_409,C_410)) ) ),
    inference(resolution,[status(thm)],[c_2136,c_2])).

tff(c_2369,plain,(
    ! [A_437,A_438,B_439,C_440] :
      ( r2_hidden(k1_mcart_1(A_437),k2_zfmisc_1(A_438,B_439))
      | ~ r2_hidden(A_437,k3_zfmisc_1(A_438,B_439,C_440)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_229])).

tff(c_2399,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_40,c_2369])).

tff(c_2413,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_2399,c_2])).

tff(c_2419,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_2158,c_2413])).

tff(c_2424,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1712,c_2419])).

tff(c_2426,plain,(
    r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_2431,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_2426,c_2])).

tff(c_2444,plain,(
    r1_tarski('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_2432])).

tff(c_2685,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2444,c_2670])).

tff(c_2701,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_2431,c_2685])).

tff(c_2765,plain,(
    ! [A_513,B_514,C_515,D_516] :
      ( k7_mcart_1(A_513,B_514,C_515,D_516) = k2_mcart_1(D_516)
      | ~ m1_subset_1(D_516,k3_zfmisc_1(A_513,B_514,C_515))
      | k1_xboole_0 = C_515
      | k1_xboole_0 = B_514
      | k1_xboole_0 = A_513 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2769,plain,
    ( k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_42,c_2765])).

tff(c_2797,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2769])).

tff(c_2803,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2797,c_2517])).

tff(c_2807,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2701,c_2803])).

tff(c_2808,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_5'
    | k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') = k2_mcart_1('#skF_9') ),
    inference(splitRight,[status(thm)],[c_2769])).

tff(c_3150,plain,(
    k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') = k2_mcart_1('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_2808])).

tff(c_2425,plain,
    ( ~ r2_hidden(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_7')
    | ~ r2_hidden(k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_2463,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_2425])).

tff(c_3155,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3150,c_2463])).

tff(c_3158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2862,c_3155])).

tff(c_3159,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2808])).

tff(c_3165,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3159])).

tff(c_3176,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3165,c_2517])).

tff(c_3180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2717,c_3176])).

tff(c_3181,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3159])).

tff(c_2871,plain,(
    ! [B_549] :
      ( r2_hidden(k2_mcart_1('#skF_9'),B_549)
      | ~ r1_tarski('#skF_8',B_549) ) ),
    inference(resolution,[status(thm)],[c_2862,c_6])).

tff(c_2948,plain,(
    ! [B_557,B_558] :
      ( r2_hidden(k2_mcart_1('#skF_9'),B_557)
      | ~ r1_tarski(B_558,B_557)
      | ~ r1_tarski('#skF_8',B_558) ) ),
    inference(resolution,[status(thm)],[c_2871,c_6])).

tff(c_2977,plain,(
    ! [A_15] :
      ( r2_hidden(k2_mcart_1('#skF_9'),A_15)
      | ~ r1_tarski('#skF_8',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_2948])).

tff(c_2995,plain,(
    ~ r1_tarski('#skF_8',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2977])).

tff(c_3184,plain,(
    ~ r1_tarski('#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3181,c_2995])).

tff(c_3199,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2442,c_3184])).

tff(c_3201,plain,(
    r1_tarski('#skF_8',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_2977])).

tff(c_2890,plain,(
    ! [B_549] :
      ( ~ v1_xboole_0(B_549)
      | ~ r1_tarski('#skF_8',B_549) ) ),
    inference(resolution,[status(thm)],[c_2871,c_2])).

tff(c_3206,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3201,c_2890])).

tff(c_3219,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2517,c_3206])).

tff(c_3220,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_2702])).

tff(c_2528,plain,(
    ! [A_466,C_467,B_468] :
      ( r2_hidden(k2_mcart_1(A_466),C_467)
      | ~ r2_hidden(A_466,k2_zfmisc_1(B_468,C_467)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3662,plain,(
    ! [B_660,C_661] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_660,C_661))),C_661)
      | v1_xboole_0(k2_zfmisc_1(B_660,C_661)) ) ),
    inference(resolution,[status(thm)],[c_4,c_2528])).

tff(c_3686,plain,(
    ! [C_662,B_663] :
      ( ~ v1_xboole_0(C_662)
      | v1_xboole_0(k2_zfmisc_1(B_663,C_662)) ) ),
    inference(resolution,[status(thm)],[c_3662,c_2])).

tff(c_2706,plain,(
    ! [A_500,B_501,C_502] :
      ( r2_hidden(k1_mcart_1(A_500),B_501)
      | ~ r2_hidden(A_500,k2_zfmisc_1(B_501,C_502)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3576,plain,(
    ! [B_646,C_647] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_646,C_647))),B_646)
      | v1_xboole_0(k2_zfmisc_1(B_646,C_647)) ) ),
    inference(resolution,[status(thm)],[c_4,c_2706])).

tff(c_3602,plain,(
    ! [B_648,C_649] :
      ( ~ v1_xboole_0(B_648)
      | v1_xboole_0(k2_zfmisc_1(B_648,C_649)) ) ),
    inference(resolution,[status(thm)],[c_3576,c_2])).

tff(c_3609,plain,(
    ! [A_653,B_654,C_655] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_653,B_654))
      | v1_xboole_0(k3_zfmisc_1(A_653,B_654,C_655)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_3602])).

tff(c_3613,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_3609,c_59])).

tff(c_3689,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_3686,c_3613])).

tff(c_3696,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3220,c_3689])).

tff(c_3697,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_2425])).

tff(c_3794,plain,(
    ! [A_682,C_683] :
      ( r1_xboole_0(A_682,C_683)
      | ~ v1_xboole_0(A_682) ) ),
    inference(resolution,[status(thm)],[c_2462,c_3733])).

tff(c_3839,plain,(
    ! [C_688,A_689] :
      ( r1_xboole_0(C_688,A_689)
      | ~ v1_xboole_0(A_689) ) ),
    inference(resolution,[status(thm)],[c_3794,c_12])).

tff(c_3898,plain,(
    ! [C_703,A_704] :
      ( ~ r1_tarski(C_703,A_704)
      | v1_xboole_0(C_703)
      | ~ v1_xboole_0(A_704) ) ),
    inference(resolution,[status(thm)],[c_3839,c_20])).

tff(c_3930,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_2443,c_3898])).

tff(c_3936,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3930])).

tff(c_3913,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2444,c_3898])).

tff(c_3929,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_2431,c_3913])).

tff(c_4039,plain,(
    ! [A_725,B_726,C_727,D_728] :
      ( k7_mcart_1(A_725,B_726,C_727,D_728) = k2_mcart_1(D_728)
      | ~ m1_subset_1(D_728,k3_zfmisc_1(A_725,B_726,C_727))
      | k1_xboole_0 = C_727
      | k1_xboole_0 = B_726
      | k1_xboole_0 = A_725 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4043,plain,
    ( k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_42,c_4039])).

tff(c_4054,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4043])).

tff(c_4060,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4054,c_3767])).

tff(c_4064,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3929,c_4060])).

tff(c_4066,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4043])).

tff(c_4094,plain,(
    ! [A_746,B_747,C_748,D_749] :
      ( k6_mcart_1(A_746,B_747,C_748,D_749) = k2_mcart_1(k1_mcart_1(D_749))
      | ~ m1_subset_1(D_749,k3_zfmisc_1(A_746,B_747,C_748))
      | k1_xboole_0 = C_748
      | k1_xboole_0 = B_747
      | k1_xboole_0 = A_746 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4097,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_9')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_42,c_4094])).

tff(c_4100,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_9')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_4066,c_4097])).

tff(c_4548,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_4100])).

tff(c_4560,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4548,c_3767])).

tff(c_4564,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3936,c_4560])).

tff(c_4565,plain,
    ( k1_xboole_0 = '#skF_5'
    | k2_mcart_1(k1_mcart_1('#skF_9')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') ),
    inference(splitRight,[status(thm)],[c_4100])).

tff(c_4627,plain,(
    k2_mcart_1(k1_mcart_1('#skF_9')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_4565])).

tff(c_3937,plain,(
    ! [A_705,B_706,C_707] : k2_zfmisc_1(k2_zfmisc_1(A_705,B_706),C_707) = k3_zfmisc_1(A_705,B_706,C_707) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4720,plain,(
    ! [A_832,A_833,B_834,C_835] :
      ( r2_hidden(k1_mcart_1(A_832),k2_zfmisc_1(A_833,B_834))
      | ~ r2_hidden(A_832,k3_zfmisc_1(A_833,B_834,C_835)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3937,c_30])).

tff(c_4758,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_40,c_4720])).

tff(c_4761,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_4758,c_28])).

tff(c_4770,plain,(
    r2_hidden(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4627,c_4761])).

tff(c_4772,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3697,c_4770])).

tff(c_4773,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_4565])).

tff(c_3992,plain,(
    ! [A_718,C_719,B_720] :
      ( r2_hidden(k2_mcart_1(A_718),C_719)
      | ~ r2_hidden(A_718,k2_zfmisc_1(B_720,C_719)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4122,plain,(
    ! [A_757,C_758,A_759,B_760] :
      ( r2_hidden(k2_mcart_1(A_757),C_758)
      | ~ r2_hidden(A_757,k3_zfmisc_1(A_759,B_760,C_758)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_3992])).

tff(c_4140,plain,(
    r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_40,c_4122])).

tff(c_4149,plain,(
    ! [B_761] :
      ( r2_hidden(k2_mcart_1('#skF_9'),B_761)
      | ~ r1_tarski('#skF_8',B_761) ) ),
    inference(resolution,[status(thm)],[c_4140,c_6])).

tff(c_4204,plain,(
    ! [B_764,B_765] :
      ( r2_hidden(k2_mcart_1('#skF_9'),B_764)
      | ~ r1_tarski(B_765,B_764)
      | ~ r1_tarski('#skF_8',B_765) ) ),
    inference(resolution,[status(thm)],[c_4149,c_6])).

tff(c_4220,plain,
    ( r2_hidden(k2_mcart_1('#skF_9'),'#skF_5')
    | ~ r1_tarski('#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_2442,c_4204])).

tff(c_4232,plain,(
    r2_hidden(k2_mcart_1('#skF_9'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3714,c_4220])).

tff(c_4263,plain,(
    ! [B_770] :
      ( r2_hidden(k2_mcart_1('#skF_9'),B_770)
      | ~ r1_tarski('#skF_5',B_770) ) ),
    inference(resolution,[status(thm)],[c_4232,c_6])).

tff(c_4361,plain,(
    ! [B_789,B_790] :
      ( r2_hidden(k2_mcart_1('#skF_9'),B_789)
      | ~ r1_tarski(B_790,B_789)
      | ~ r1_tarski('#skF_5',B_790) ) ),
    inference(resolution,[status(thm)],[c_4263,c_6])).

tff(c_4389,plain,(
    ! [A_15] :
      ( r2_hidden(k2_mcart_1('#skF_9'),A_15)
      | ~ r1_tarski('#skF_5',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_4361])).

tff(c_4437,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_4389])).

tff(c_4776,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4773,c_4437])).

tff(c_4792,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3714,c_4776])).

tff(c_4794,plain,(
    r1_tarski('#skF_5',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_4389])).

tff(c_4282,plain,(
    ! [B_770] :
      ( ~ v1_xboole_0(B_770)
      | ~ r1_tarski('#skF_5',B_770) ) ),
    inference(resolution,[status(thm)],[c_4263,c_2])).

tff(c_4799,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4794,c_4282])).

tff(c_4814,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3767,c_4799])).

tff(c_4815,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_3930])).

tff(c_4854,plain,(
    ! [A_843,C_844,B_845] :
      ( r2_hidden(k2_mcart_1(A_843),C_844)
      | ~ r2_hidden(A_843,k2_zfmisc_1(B_845,C_844)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_5312,plain,(
    ! [B_923,C_924] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_923,C_924))),C_924)
      | v1_xboole_0(k2_zfmisc_1(B_923,C_924)) ) ),
    inference(resolution,[status(thm)],[c_4,c_4854])).

tff(c_5382,plain,(
    ! [C_927,B_928] :
      ( ~ v1_xboole_0(C_927)
      | v1_xboole_0(k2_zfmisc_1(B_928,C_927)) ) ),
    inference(resolution,[status(thm)],[c_5312,c_2])).

tff(c_3847,plain,(
    ! [A_690,B_691,C_692] :
      ( r2_hidden(k1_mcart_1(A_690),B_691)
      | ~ r2_hidden(A_690,k2_zfmisc_1(B_691,C_692)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_5203,plain,(
    ! [B_913,C_914] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_913,C_914))),B_913)
      | v1_xboole_0(k2_zfmisc_1(B_913,C_914)) ) ),
    inference(resolution,[status(thm)],[c_4,c_3847])).

tff(c_5229,plain,(
    ! [B_915,C_916] :
      ( ~ v1_xboole_0(B_915)
      | v1_xboole_0(k2_zfmisc_1(B_915,C_916)) ) ),
    inference(resolution,[status(thm)],[c_5203,c_2])).

tff(c_5233,plain,(
    ! [A_917,B_918,C_919] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_917,B_918))
      | v1_xboole_0(k3_zfmisc_1(A_917,B_918,C_919)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_5229])).

tff(c_5237,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_5233,c_59])).

tff(c_5385,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_5382,c_5237])).

tff(c_5392,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4815,c_5385])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:18:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.98/2.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.27/2.23  
% 6.27/2.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.27/2.23  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2
% 6.27/2.23  
% 6.27/2.23  %Foreground sorts:
% 6.27/2.23  
% 6.27/2.23  
% 6.27/2.23  %Background operators:
% 6.27/2.23  
% 6.27/2.23  
% 6.27/2.23  %Foreground operators:
% 6.27/2.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.27/2.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.27/2.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.27/2.23  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.27/2.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.27/2.23  tff('#skF_7', type, '#skF_7': $i).
% 6.27/2.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.27/2.23  tff('#skF_5', type, '#skF_5': $i).
% 6.27/2.23  tff('#skF_6', type, '#skF_6': $i).
% 6.27/2.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.27/2.23  tff('#skF_3', type, '#skF_3': $i).
% 6.27/2.23  tff('#skF_9', type, '#skF_9': $i).
% 6.27/2.23  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 6.27/2.23  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 6.27/2.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.27/2.23  tff('#skF_8', type, '#skF_8': $i).
% 6.27/2.23  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 6.27/2.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.27/2.23  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 6.27/2.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.27/2.23  tff('#skF_4', type, '#skF_4': $i).
% 6.27/2.23  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 6.27/2.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.27/2.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.27/2.23  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 6.27/2.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.27/2.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.27/2.23  
% 6.27/2.26  tff(f_50, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.27/2.26  tff(f_48, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 6.27/2.26  tff(f_58, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 6.27/2.26  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.27/2.26  tff(f_110, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (![F]: (m1_subset_1(F, k1_zfmisc_1(C)) => (![G]: (m1_subset_1(G, k3_zfmisc_1(A, B, C)) => (r2_hidden(G, k3_zfmisc_1(D, E, F)) => ((r2_hidden(k5_mcart_1(A, B, C, G), D) & r2_hidden(k6_mcart_1(A, B, C, G), E)) & r2_hidden(k7_mcart_1(A, B, C, G), F))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_mcart_1)).
% 6.27/2.26  tff(f_62, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.27/2.26  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.27/2.26  tff(f_42, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 6.27/2.26  tff(f_64, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 6.27/2.26  tff(f_70, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 6.27/2.26  tff(f_90, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 6.27/2.26  tff(c_18, plain, (![A_15]: (r1_tarski(k1_xboole_0, A_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.27/2.26  tff(c_3733, plain, (![A_674, C_675, B_676]: (r1_xboole_0(A_674, C_675) | ~r1_tarski(A_674, k4_xboole_0(B_676, C_675)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.27/2.26  tff(c_3759, plain, (![C_677]: (r1_xboole_0(k1_xboole_0, C_677))), inference(resolution, [status(thm)], [c_18, c_3733])).
% 6.27/2.26  tff(c_20, plain, (![B_17, A_16]: (~r1_xboole_0(B_17, A_16) | ~r1_tarski(B_17, A_16) | v1_xboole_0(B_17))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.27/2.26  tff(c_3762, plain, (![C_677]: (~r1_tarski(k1_xboole_0, C_677) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_3759, c_20])).
% 6.27/2.26  tff(c_3767, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_3762])).
% 6.27/2.26  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.27/2.26  tff(c_3709, plain, (![A_666, B_667]: (~r2_hidden('#skF_2'(A_666, B_667), B_667) | r1_tarski(A_666, B_667))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.27/2.26  tff(c_3714, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_10, c_3709])).
% 6.27/2.26  tff(c_2488, plain, (![A_461, C_462, B_463]: (r1_xboole_0(A_461, C_462) | ~r1_tarski(A_461, k4_xboole_0(B_463, C_462)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.27/2.26  tff(c_2509, plain, (![C_464]: (r1_xboole_0(k1_xboole_0, C_464))), inference(resolution, [status(thm)], [c_18, c_2488])).
% 6.27/2.26  tff(c_2512, plain, (![C_464]: (~r1_tarski(k1_xboole_0, C_464) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_2509, c_20])).
% 6.27/2.26  tff(c_2517, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2512])).
% 6.27/2.26  tff(c_44, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.27/2.26  tff(c_2432, plain, (![A_443, B_444]: (r1_tarski(A_443, B_444) | ~m1_subset_1(A_443, k1_zfmisc_1(B_444)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.27/2.26  tff(c_2442, plain, (r1_tarski('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_2432])).
% 6.27/2.26  tff(c_46, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.27/2.26  tff(c_2443, plain, (r1_tarski('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_2432])).
% 6.27/2.26  tff(c_2458, plain, (![A_452, B_453]: (r2_hidden('#skF_2'(A_452, B_453), A_452) | r1_tarski(A_452, B_453))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.27/2.26  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.27/2.26  tff(c_2462, plain, (![A_452, B_453]: (~v1_xboole_0(A_452) | r1_tarski(A_452, B_453))), inference(resolution, [status(thm)], [c_2458, c_2])).
% 6.27/2.26  tff(c_2545, plain, (![A_471, C_472]: (r1_xboole_0(A_471, C_472) | ~v1_xboole_0(A_471))), inference(resolution, [status(thm)], [c_2462, c_2488])).
% 6.27/2.26  tff(c_12, plain, (![B_11, A_10]: (r1_xboole_0(B_11, A_10) | ~r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.27/2.26  tff(c_2603, plain, (![C_480, A_481]: (r1_xboole_0(C_480, A_481) | ~v1_xboole_0(A_481))), inference(resolution, [status(thm)], [c_2545, c_12])).
% 6.27/2.26  tff(c_2670, plain, (![C_498, A_499]: (~r1_tarski(C_498, A_499) | v1_xboole_0(C_498) | ~v1_xboole_0(A_499))), inference(resolution, [status(thm)], [c_2603, c_20])).
% 6.27/2.26  tff(c_2702, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_2443, c_2670])).
% 6.27/2.26  tff(c_2717, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_2702])).
% 6.27/2.26  tff(c_40, plain, (r2_hidden('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.27/2.26  tff(c_2586, plain, (![A_477, B_478, C_479]: (k2_zfmisc_1(k2_zfmisc_1(A_477, B_478), C_479)=k3_zfmisc_1(A_477, B_478, C_479))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.27/2.26  tff(c_28, plain, (![A_23, C_25, B_24]: (r2_hidden(k2_mcart_1(A_23), C_25) | ~r2_hidden(A_23, k2_zfmisc_1(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.27/2.26  tff(c_2848, plain, (![A_545, C_546, A_547, B_548]: (r2_hidden(k2_mcart_1(A_545), C_546) | ~r2_hidden(A_545, k3_zfmisc_1(A_547, B_548, C_546)))), inference(superposition, [status(thm), theory('equality')], [c_2586, c_28])).
% 6.27/2.26  tff(c_2862, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_40, c_2848])).
% 6.27/2.26  tff(c_94, plain, (![A_61, C_62, B_63]: (r1_xboole_0(A_61, C_62) | ~r1_tarski(A_61, k4_xboole_0(B_63, C_62)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.27/2.26  tff(c_110, plain, (![C_64]: (r1_xboole_0(k1_xboole_0, C_64))), inference(resolution, [status(thm)], [c_18, c_94])).
% 6.27/2.26  tff(c_113, plain, (![C_64]: (~r1_tarski(k1_xboole_0, C_64) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_110, c_20])).
% 6.27/2.26  tff(c_118, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_113])).
% 6.27/2.26  tff(c_87, plain, (![A_58, B_59]: (~r2_hidden('#skF_2'(A_58, B_59), B_59) | r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.27/2.26  tff(c_92, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_10, c_87])).
% 6.27/2.26  tff(c_38, plain, (~r2_hidden(k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_8') | ~r2_hidden(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_7') | ~r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.27/2.26  tff(c_60, plain, (~r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_6')), inference(splitLeft, [status(thm)], [c_38])).
% 6.27/2.26  tff(c_63, plain, (![A_50, B_51]: (r1_tarski(A_50, B_51) | ~m1_subset_1(A_50, k1_zfmisc_1(B_51)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.27/2.26  tff(c_78, plain, (r1_tarski('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_63])).
% 6.27/2.26  tff(c_80, plain, (![A_52, B_53]: (r2_hidden('#skF_2'(A_52, B_53), A_52) | r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.27/2.26  tff(c_84, plain, (![A_52, B_53]: (~v1_xboole_0(A_52) | r1_tarski(A_52, B_53))), inference(resolution, [status(thm)], [c_80, c_2])).
% 6.27/2.26  tff(c_157, plain, (![A_71, C_72]: (r1_xboole_0(A_71, C_72) | ~v1_xboole_0(A_71))), inference(resolution, [status(thm)], [c_84, c_94])).
% 6.27/2.26  tff(c_188, plain, (![C_78, A_79]: (r1_xboole_0(C_78, A_79) | ~v1_xboole_0(A_79))), inference(resolution, [status(thm)], [c_157, c_12])).
% 6.27/2.26  tff(c_288, plain, (![C_100, A_101]: (~r1_tarski(C_100, A_101) | v1_xboole_0(C_100) | ~v1_xboole_0(A_101))), inference(resolution, [status(thm)], [c_188, c_20])).
% 6.27/2.26  tff(c_317, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_78, c_288])).
% 6.27/2.26  tff(c_322, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_317])).
% 6.27/2.26  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.27/2.26  tff(c_79, plain, (r1_tarski('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_63])).
% 6.27/2.26  tff(c_318, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_79, c_288])).
% 6.27/2.26  tff(c_323, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_318])).
% 6.27/2.26  tff(c_42, plain, (m1_subset_1('#skF_9', k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.27/2.26  tff(c_390, plain, (![A_118, B_119, C_120, D_121]: (k7_mcart_1(A_118, B_119, C_120, D_121)=k2_mcart_1(D_121) | ~m1_subset_1(D_121, k3_zfmisc_1(A_118, B_119, C_120)) | k1_xboole_0=C_120 | k1_xboole_0=B_119 | k1_xboole_0=A_118)), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.27/2.26  tff(c_394, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_42, c_390])).
% 6.27/2.26  tff(c_422, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_394])).
% 6.27/2.26  tff(c_428, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_422, c_118])).
% 6.27/2.26  tff(c_432, plain, $false, inference(negUnitSimplification, [status(thm)], [c_323, c_428])).
% 6.27/2.26  tff(c_434, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_394])).
% 6.27/2.26  tff(c_568, plain, (![A_158, B_159, C_160, D_161]: (k5_mcart_1(A_158, B_159, C_160, D_161)=k1_mcart_1(k1_mcart_1(D_161)) | ~m1_subset_1(D_161, k3_zfmisc_1(A_158, B_159, C_160)) | k1_xboole_0=C_160 | k1_xboole_0=B_159 | k1_xboole_0=A_158)), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.27/2.26  tff(c_571, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_42, c_568])).
% 6.27/2.26  tff(c_574, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_434, c_571])).
% 6.27/2.26  tff(c_880, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_574])).
% 6.27/2.26  tff(c_892, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_880, c_118])).
% 6.27/2.26  tff(c_896, plain, $false, inference(negUnitSimplification, [status(thm)], [c_322, c_892])).
% 6.27/2.26  tff(c_897, plain, (k1_xboole_0='#skF_5' | k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')), inference(splitRight, [status(thm)], [c_574])).
% 6.27/2.26  tff(c_943, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')), inference(splitLeft, [status(thm)], [c_897])).
% 6.27/2.26  tff(c_26, plain, (![A_20, B_21, C_22]: (k2_zfmisc_1(k2_zfmisc_1(A_20, B_21), C_22)=k3_zfmisc_1(A_20, B_21, C_22))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.27/2.26  tff(c_229, plain, (![A_84, B_85, C_86]: (r2_hidden(k1_mcart_1(A_84), B_85) | ~r2_hidden(A_84, k2_zfmisc_1(B_85, C_86)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.27/2.26  tff(c_1147, plain, (![A_248, A_249, B_250, C_251]: (r2_hidden(k1_mcart_1(A_248), k2_zfmisc_1(A_249, B_250)) | ~r2_hidden(A_248, k3_zfmisc_1(A_249, B_250, C_251)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_229])).
% 6.27/2.26  tff(c_1184, plain, (r2_hidden(k1_mcart_1('#skF_9'), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_40, c_1147])).
% 6.27/2.26  tff(c_30, plain, (![A_23, B_24, C_25]: (r2_hidden(k1_mcart_1(A_23), B_24) | ~r2_hidden(A_23, k2_zfmisc_1(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.27/2.26  tff(c_1191, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')), '#skF_6')), inference(resolution, [status(thm)], [c_1184, c_30])).
% 6.27/2.26  tff(c_1199, plain, (r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_943, c_1191])).
% 6.27/2.26  tff(c_1201, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_1199])).
% 6.27/2.26  tff(c_1202, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_897])).
% 6.27/2.26  tff(c_77, plain, (r1_tarski('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_63])).
% 6.27/2.26  tff(c_265, plain, (![A_95, C_96, B_97]: (r2_hidden(k2_mcart_1(A_95), C_96) | ~r2_hidden(A_95, k2_zfmisc_1(B_97, C_96)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.27/2.26  tff(c_473, plain, (![A_150, C_151, A_152, B_153]: (r2_hidden(k2_mcart_1(A_150), C_151) | ~r2_hidden(A_150, k3_zfmisc_1(A_152, B_153, C_151)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_265])).
% 6.27/2.26  tff(c_487, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_40, c_473])).
% 6.27/2.26  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.27/2.26  tff(c_496, plain, (![B_154]: (r2_hidden(k2_mcart_1('#skF_9'), B_154) | ~r1_tarski('#skF_8', B_154))), inference(resolution, [status(thm)], [c_487, c_6])).
% 6.27/2.26  tff(c_531, plain, (![B_156, B_157]: (r2_hidden(k2_mcart_1('#skF_9'), B_156) | ~r1_tarski(B_157, B_156) | ~r1_tarski('#skF_8', B_157))), inference(resolution, [status(thm)], [c_496, c_6])).
% 6.27/2.26  tff(c_547, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_5') | ~r1_tarski('#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_77, c_531])).
% 6.27/2.26  tff(c_559, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_547])).
% 6.27/2.26  tff(c_590, plain, (![B_162]: (r2_hidden(k2_mcart_1('#skF_9'), B_162) | ~r1_tarski('#skF_5', B_162))), inference(resolution, [status(thm)], [c_559, c_6])).
% 6.27/2.26  tff(c_679, plain, (![B_181, B_182]: (r2_hidden(k2_mcart_1('#skF_9'), B_181) | ~r1_tarski(B_182, B_181) | ~r1_tarski('#skF_5', B_182))), inference(resolution, [status(thm)], [c_590, c_6])).
% 6.27/2.26  tff(c_707, plain, (![A_15]: (r2_hidden(k2_mcart_1('#skF_9'), A_15) | ~r1_tarski('#skF_5', k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_679])).
% 6.27/2.26  tff(c_738, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_707])).
% 6.27/2.26  tff(c_1205, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1202, c_738])).
% 6.27/2.26  tff(c_1221, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_1205])).
% 6.27/2.26  tff(c_1223, plain, (r1_tarski('#skF_5', k1_xboole_0)), inference(splitRight, [status(thm)], [c_707])).
% 6.27/2.26  tff(c_609, plain, (![B_162]: (~v1_xboole_0(B_162) | ~r1_tarski('#skF_5', B_162))), inference(resolution, [status(thm)], [c_590, c_2])).
% 6.27/2.26  tff(c_1228, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_1223, c_609])).
% 6.27/2.26  tff(c_1243, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_1228])).
% 6.27/2.26  tff(c_1244, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_318])).
% 6.27/2.26  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.27/2.26  tff(c_1601, plain, (![B_326, C_327]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_326, C_327))), B_326) | v1_xboole_0(k2_zfmisc_1(B_326, C_327)))), inference(resolution, [status(thm)], [c_4, c_229])).
% 6.27/2.26  tff(c_1625, plain, (![B_326, C_327]: (~v1_xboole_0(B_326) | v1_xboole_0(k2_zfmisc_1(B_326, C_327)))), inference(resolution, [status(thm)], [c_1601, c_2])).
% 6.27/2.26  tff(c_1631, plain, (![B_328, C_329]: (~v1_xboole_0(B_328) | v1_xboole_0(k2_zfmisc_1(B_328, C_329)))), inference(resolution, [status(thm)], [c_1601, c_2])).
% 6.27/2.26  tff(c_1676, plain, (![A_332, B_333, C_334]: (~v1_xboole_0(k2_zfmisc_1(A_332, B_333)) | v1_xboole_0(k3_zfmisc_1(A_332, B_333, C_334)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1631])).
% 6.27/2.26  tff(c_59, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_40, c_2])).
% 6.27/2.26  tff(c_1680, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_1676, c_59])).
% 6.27/2.26  tff(c_1707, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_1625, c_1680])).
% 6.27/2.26  tff(c_1711, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1244, c_1707])).
% 6.27/2.26  tff(c_1712, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_317])).
% 6.27/2.26  tff(c_2136, plain, (![B_409, C_410]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_409, C_410))), C_410) | v1_xboole_0(k2_zfmisc_1(B_409, C_410)))), inference(resolution, [status(thm)], [c_4, c_265])).
% 6.27/2.26  tff(c_2158, plain, (![C_410, B_409]: (~v1_xboole_0(C_410) | v1_xboole_0(k2_zfmisc_1(B_409, C_410)))), inference(resolution, [status(thm)], [c_2136, c_2])).
% 6.27/2.26  tff(c_2369, plain, (![A_437, A_438, B_439, C_440]: (r2_hidden(k1_mcart_1(A_437), k2_zfmisc_1(A_438, B_439)) | ~r2_hidden(A_437, k3_zfmisc_1(A_438, B_439, C_440)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_229])).
% 6.27/2.26  tff(c_2399, plain, (r2_hidden(k1_mcart_1('#skF_9'), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_40, c_2369])).
% 6.27/2.26  tff(c_2413, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_2399, c_2])).
% 6.27/2.26  tff(c_2419, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_2158, c_2413])).
% 6.27/2.26  tff(c_2424, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1712, c_2419])).
% 6.27/2.26  tff(c_2426, plain, (r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_6')), inference(splitRight, [status(thm)], [c_38])).
% 6.27/2.26  tff(c_2431, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_2426, c_2])).
% 6.27/2.26  tff(c_2444, plain, (r1_tarski('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_2432])).
% 6.27/2.26  tff(c_2685, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_2444, c_2670])).
% 6.27/2.26  tff(c_2701, plain, (~v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_2431, c_2685])).
% 6.27/2.26  tff(c_2765, plain, (![A_513, B_514, C_515, D_516]: (k7_mcart_1(A_513, B_514, C_515, D_516)=k2_mcart_1(D_516) | ~m1_subset_1(D_516, k3_zfmisc_1(A_513, B_514, C_515)) | k1_xboole_0=C_515 | k1_xboole_0=B_514 | k1_xboole_0=A_513)), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.27/2.26  tff(c_2769, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_42, c_2765])).
% 6.27/2.26  tff(c_2797, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2769])).
% 6.27/2.26  tff(c_2803, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2797, c_2517])).
% 6.27/2.26  tff(c_2807, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2701, c_2803])).
% 6.27/2.26  tff(c_2808, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_5' | k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')=k2_mcart_1('#skF_9')), inference(splitRight, [status(thm)], [c_2769])).
% 6.27/2.26  tff(c_3150, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')=k2_mcart_1('#skF_9')), inference(splitLeft, [status(thm)], [c_2808])).
% 6.27/2.26  tff(c_2425, plain, (~r2_hidden(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_7') | ~r2_hidden(k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_38])).
% 6.27/2.26  tff(c_2463, plain, (~r2_hidden(k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_8')), inference(splitLeft, [status(thm)], [c_2425])).
% 6.27/2.26  tff(c_3155, plain, (~r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3150, c_2463])).
% 6.27/2.26  tff(c_3158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2862, c_3155])).
% 6.27/2.26  tff(c_3159, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_2808])).
% 6.27/2.26  tff(c_3165, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_3159])).
% 6.27/2.26  tff(c_3176, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3165, c_2517])).
% 6.27/2.26  tff(c_3180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2717, c_3176])).
% 6.27/2.26  tff(c_3181, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_3159])).
% 6.27/2.26  tff(c_2871, plain, (![B_549]: (r2_hidden(k2_mcart_1('#skF_9'), B_549) | ~r1_tarski('#skF_8', B_549))), inference(resolution, [status(thm)], [c_2862, c_6])).
% 6.27/2.26  tff(c_2948, plain, (![B_557, B_558]: (r2_hidden(k2_mcart_1('#skF_9'), B_557) | ~r1_tarski(B_558, B_557) | ~r1_tarski('#skF_8', B_558))), inference(resolution, [status(thm)], [c_2871, c_6])).
% 6.27/2.26  tff(c_2977, plain, (![A_15]: (r2_hidden(k2_mcart_1('#skF_9'), A_15) | ~r1_tarski('#skF_8', k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_2948])).
% 6.27/2.26  tff(c_2995, plain, (~r1_tarski('#skF_8', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_2977])).
% 6.27/2.26  tff(c_3184, plain, (~r1_tarski('#skF_8', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3181, c_2995])).
% 6.27/2.26  tff(c_3199, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2442, c_3184])).
% 6.27/2.26  tff(c_3201, plain, (r1_tarski('#skF_8', k1_xboole_0)), inference(splitRight, [status(thm)], [c_2977])).
% 6.27/2.26  tff(c_2890, plain, (![B_549]: (~v1_xboole_0(B_549) | ~r1_tarski('#skF_8', B_549))), inference(resolution, [status(thm)], [c_2871, c_2])).
% 6.27/2.26  tff(c_3206, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_3201, c_2890])).
% 6.27/2.26  tff(c_3219, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2517, c_3206])).
% 6.27/2.26  tff(c_3220, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_2702])).
% 6.27/2.26  tff(c_2528, plain, (![A_466, C_467, B_468]: (r2_hidden(k2_mcart_1(A_466), C_467) | ~r2_hidden(A_466, k2_zfmisc_1(B_468, C_467)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.27/2.26  tff(c_3662, plain, (![B_660, C_661]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_660, C_661))), C_661) | v1_xboole_0(k2_zfmisc_1(B_660, C_661)))), inference(resolution, [status(thm)], [c_4, c_2528])).
% 6.27/2.26  tff(c_3686, plain, (![C_662, B_663]: (~v1_xboole_0(C_662) | v1_xboole_0(k2_zfmisc_1(B_663, C_662)))), inference(resolution, [status(thm)], [c_3662, c_2])).
% 6.27/2.26  tff(c_2706, plain, (![A_500, B_501, C_502]: (r2_hidden(k1_mcart_1(A_500), B_501) | ~r2_hidden(A_500, k2_zfmisc_1(B_501, C_502)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.27/2.26  tff(c_3576, plain, (![B_646, C_647]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_646, C_647))), B_646) | v1_xboole_0(k2_zfmisc_1(B_646, C_647)))), inference(resolution, [status(thm)], [c_4, c_2706])).
% 6.27/2.26  tff(c_3602, plain, (![B_648, C_649]: (~v1_xboole_0(B_648) | v1_xboole_0(k2_zfmisc_1(B_648, C_649)))), inference(resolution, [status(thm)], [c_3576, c_2])).
% 6.27/2.26  tff(c_3609, plain, (![A_653, B_654, C_655]: (~v1_xboole_0(k2_zfmisc_1(A_653, B_654)) | v1_xboole_0(k3_zfmisc_1(A_653, B_654, C_655)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_3602])).
% 6.27/2.26  tff(c_3613, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_3609, c_59])).
% 6.27/2.26  tff(c_3689, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_3686, c_3613])).
% 6.27/2.26  tff(c_3696, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3220, c_3689])).
% 6.27/2.26  tff(c_3697, plain, (~r2_hidden(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_7')), inference(splitRight, [status(thm)], [c_2425])).
% 6.27/2.26  tff(c_3794, plain, (![A_682, C_683]: (r1_xboole_0(A_682, C_683) | ~v1_xboole_0(A_682))), inference(resolution, [status(thm)], [c_2462, c_3733])).
% 6.27/2.26  tff(c_3839, plain, (![C_688, A_689]: (r1_xboole_0(C_688, A_689) | ~v1_xboole_0(A_689))), inference(resolution, [status(thm)], [c_3794, c_12])).
% 6.27/2.26  tff(c_3898, plain, (![C_703, A_704]: (~r1_tarski(C_703, A_704) | v1_xboole_0(C_703) | ~v1_xboole_0(A_704))), inference(resolution, [status(thm)], [c_3839, c_20])).
% 6.27/2.26  tff(c_3930, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_2443, c_3898])).
% 6.27/2.26  tff(c_3936, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_3930])).
% 6.27/2.26  tff(c_3913, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_2444, c_3898])).
% 6.27/2.26  tff(c_3929, plain, (~v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_2431, c_3913])).
% 6.27/2.26  tff(c_4039, plain, (![A_725, B_726, C_727, D_728]: (k7_mcart_1(A_725, B_726, C_727, D_728)=k2_mcart_1(D_728) | ~m1_subset_1(D_728, k3_zfmisc_1(A_725, B_726, C_727)) | k1_xboole_0=C_727 | k1_xboole_0=B_726 | k1_xboole_0=A_725)), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.27/2.26  tff(c_4043, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_42, c_4039])).
% 6.27/2.26  tff(c_4054, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_4043])).
% 6.27/2.26  tff(c_4060, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4054, c_3767])).
% 6.27/2.26  tff(c_4064, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3929, c_4060])).
% 6.27/2.26  tff(c_4066, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_4043])).
% 6.27/2.26  tff(c_4094, plain, (![A_746, B_747, C_748, D_749]: (k6_mcart_1(A_746, B_747, C_748, D_749)=k2_mcart_1(k1_mcart_1(D_749)) | ~m1_subset_1(D_749, k3_zfmisc_1(A_746, B_747, C_748)) | k1_xboole_0=C_748 | k1_xboole_0=B_747 | k1_xboole_0=A_746)), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.27/2.26  tff(c_4097, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_42, c_4094])).
% 6.27/2.26  tff(c_4100, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_4066, c_4097])).
% 6.27/2.26  tff(c_4548, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_4100])).
% 6.27/2.26  tff(c_4560, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4548, c_3767])).
% 6.27/2.26  tff(c_4564, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3936, c_4560])).
% 6.27/2.26  tff(c_4565, plain, (k1_xboole_0='#skF_5' | k2_mcart_1(k1_mcart_1('#skF_9'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')), inference(splitRight, [status(thm)], [c_4100])).
% 6.27/2.26  tff(c_4627, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')), inference(splitLeft, [status(thm)], [c_4565])).
% 6.27/2.26  tff(c_3937, plain, (![A_705, B_706, C_707]: (k2_zfmisc_1(k2_zfmisc_1(A_705, B_706), C_707)=k3_zfmisc_1(A_705, B_706, C_707))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.27/2.26  tff(c_4720, plain, (![A_832, A_833, B_834, C_835]: (r2_hidden(k1_mcart_1(A_832), k2_zfmisc_1(A_833, B_834)) | ~r2_hidden(A_832, k3_zfmisc_1(A_833, B_834, C_835)))), inference(superposition, [status(thm), theory('equality')], [c_3937, c_30])).
% 6.27/2.26  tff(c_4758, plain, (r2_hidden(k1_mcart_1('#skF_9'), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_40, c_4720])).
% 6.27/2.26  tff(c_4761, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')), '#skF_7')), inference(resolution, [status(thm)], [c_4758, c_28])).
% 6.27/2.26  tff(c_4770, plain, (r2_hidden(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_4627, c_4761])).
% 6.27/2.26  tff(c_4772, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3697, c_4770])).
% 6.27/2.26  tff(c_4773, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_4565])).
% 6.27/2.26  tff(c_3992, plain, (![A_718, C_719, B_720]: (r2_hidden(k2_mcart_1(A_718), C_719) | ~r2_hidden(A_718, k2_zfmisc_1(B_720, C_719)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.27/2.26  tff(c_4122, plain, (![A_757, C_758, A_759, B_760]: (r2_hidden(k2_mcart_1(A_757), C_758) | ~r2_hidden(A_757, k3_zfmisc_1(A_759, B_760, C_758)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_3992])).
% 6.27/2.26  tff(c_4140, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_40, c_4122])).
% 6.27/2.26  tff(c_4149, plain, (![B_761]: (r2_hidden(k2_mcart_1('#skF_9'), B_761) | ~r1_tarski('#skF_8', B_761))), inference(resolution, [status(thm)], [c_4140, c_6])).
% 6.27/2.26  tff(c_4204, plain, (![B_764, B_765]: (r2_hidden(k2_mcart_1('#skF_9'), B_764) | ~r1_tarski(B_765, B_764) | ~r1_tarski('#skF_8', B_765))), inference(resolution, [status(thm)], [c_4149, c_6])).
% 6.27/2.26  tff(c_4220, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_5') | ~r1_tarski('#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_2442, c_4204])).
% 6.27/2.26  tff(c_4232, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3714, c_4220])).
% 6.27/2.26  tff(c_4263, plain, (![B_770]: (r2_hidden(k2_mcart_1('#skF_9'), B_770) | ~r1_tarski('#skF_5', B_770))), inference(resolution, [status(thm)], [c_4232, c_6])).
% 6.27/2.26  tff(c_4361, plain, (![B_789, B_790]: (r2_hidden(k2_mcart_1('#skF_9'), B_789) | ~r1_tarski(B_790, B_789) | ~r1_tarski('#skF_5', B_790))), inference(resolution, [status(thm)], [c_4263, c_6])).
% 6.27/2.26  tff(c_4389, plain, (![A_15]: (r2_hidden(k2_mcart_1('#skF_9'), A_15) | ~r1_tarski('#skF_5', k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_4361])).
% 6.27/2.26  tff(c_4437, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_4389])).
% 6.27/2.26  tff(c_4776, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4773, c_4437])).
% 6.27/2.26  tff(c_4792, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3714, c_4776])).
% 6.27/2.26  tff(c_4794, plain, (r1_tarski('#skF_5', k1_xboole_0)), inference(splitRight, [status(thm)], [c_4389])).
% 6.27/2.26  tff(c_4282, plain, (![B_770]: (~v1_xboole_0(B_770) | ~r1_tarski('#skF_5', B_770))), inference(resolution, [status(thm)], [c_4263, c_2])).
% 6.27/2.26  tff(c_4799, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4794, c_4282])).
% 6.27/2.26  tff(c_4814, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3767, c_4799])).
% 6.27/2.26  tff(c_4815, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_3930])).
% 6.27/2.26  tff(c_4854, plain, (![A_843, C_844, B_845]: (r2_hidden(k2_mcart_1(A_843), C_844) | ~r2_hidden(A_843, k2_zfmisc_1(B_845, C_844)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.27/2.26  tff(c_5312, plain, (![B_923, C_924]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_923, C_924))), C_924) | v1_xboole_0(k2_zfmisc_1(B_923, C_924)))), inference(resolution, [status(thm)], [c_4, c_4854])).
% 6.27/2.26  tff(c_5382, plain, (![C_927, B_928]: (~v1_xboole_0(C_927) | v1_xboole_0(k2_zfmisc_1(B_928, C_927)))), inference(resolution, [status(thm)], [c_5312, c_2])).
% 6.27/2.26  tff(c_3847, plain, (![A_690, B_691, C_692]: (r2_hidden(k1_mcart_1(A_690), B_691) | ~r2_hidden(A_690, k2_zfmisc_1(B_691, C_692)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.27/2.26  tff(c_5203, plain, (![B_913, C_914]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_913, C_914))), B_913) | v1_xboole_0(k2_zfmisc_1(B_913, C_914)))), inference(resolution, [status(thm)], [c_4, c_3847])).
% 6.27/2.26  tff(c_5229, plain, (![B_915, C_916]: (~v1_xboole_0(B_915) | v1_xboole_0(k2_zfmisc_1(B_915, C_916)))), inference(resolution, [status(thm)], [c_5203, c_2])).
% 6.27/2.26  tff(c_5233, plain, (![A_917, B_918, C_919]: (~v1_xboole_0(k2_zfmisc_1(A_917, B_918)) | v1_xboole_0(k3_zfmisc_1(A_917, B_918, C_919)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_5229])).
% 6.27/2.26  tff(c_5237, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_5233, c_59])).
% 6.27/2.26  tff(c_5385, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_5382, c_5237])).
% 6.27/2.26  tff(c_5392, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4815, c_5385])).
% 6.27/2.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.27/2.26  
% 6.27/2.26  Inference rules
% 6.27/2.26  ----------------------
% 6.27/2.26  #Ref     : 0
% 6.27/2.26  #Sup     : 1132
% 6.27/2.26  #Fact    : 0
% 6.27/2.26  #Define  : 0
% 6.27/2.26  #Split   : 60
% 6.27/2.26  #Chain   : 0
% 6.27/2.26  #Close   : 0
% 6.27/2.26  
% 6.27/2.26  Ordering : KBO
% 6.27/2.26  
% 6.27/2.26  Simplification rules
% 6.27/2.26  ----------------------
% 6.27/2.26  #Subsume      : 233
% 6.27/2.26  #Demod        : 520
% 6.27/2.26  #Tautology    : 207
% 6.27/2.26  #SimpNegUnit  : 28
% 6.27/2.26  #BackRed      : 219
% 6.27/2.26  
% 6.27/2.26  #Partial instantiations: 0
% 6.27/2.26  #Strategies tried      : 1
% 6.27/2.26  
% 6.27/2.26  Timing (in seconds)
% 6.27/2.26  ----------------------
% 6.27/2.26  Preprocessing        : 0.29
% 6.27/2.26  Parsing              : 0.15
% 6.27/2.26  CNF conversion       : 0.02
% 6.27/2.26  Main loop            : 1.08
% 6.27/2.26  Inferencing          : 0.39
% 6.27/2.26  Reduction            : 0.36
% 6.27/2.26  Demodulation         : 0.25
% 6.27/2.26  BG Simplification    : 0.04
% 6.27/2.26  Subsumption          : 0.20
% 6.27/2.26  Abstraction          : 0.04
% 6.27/2.26  MUC search           : 0.00
% 6.27/2.26  Cooper               : 0.00
% 6.27/2.26  Total                : 1.45
% 6.27/2.26  Index Insertion      : 0.00
% 6.27/2.26  Index Deletion       : 0.00
% 6.27/2.26  Index Matching       : 0.00
% 6.27/2.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
