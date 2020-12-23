%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:13 EST 2020

% Result     : Theorem 4.68s
% Output     : CNFRefutation 5.02s
% Verified   : 
% Statistics : Number of formulae       :  232 ( 787 expanded)
%              Number of leaves         :   35 ( 262 expanded)
%              Depth                    :   15
%              Number of atoms          :  363 (2191 expanded)
%              Number of equality atoms :  116 ( 600 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_103,negated_conjecture,(
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

tff(f_55,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_83,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_57,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2817,plain,(
    ! [C_452,B_453,A_454] :
      ( ~ v1_xboole_0(C_452)
      | ~ m1_subset_1(B_453,k1_zfmisc_1(C_452))
      | ~ r2_hidden(A_454,B_453) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2827,plain,(
    ! [A_454] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_454,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_38,c_2817])).

tff(c_2830,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2827])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2828,plain,(
    ! [A_454] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_454,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40,c_2817])).

tff(c_2837,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2828])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2829,plain,(
    ! [A_454] :
      ( ~ v1_xboole_0('#skF_2')
      | ~ r2_hidden(A_454,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_42,c_2817])).

tff(c_2836,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2829])).

tff(c_36,plain,(
    m1_subset_1('#skF_8',k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2831,plain,(
    ! [A_455,B_456,C_457,D_458] :
      ( k7_mcart_1(A_455,B_456,C_457,D_458) = k2_mcart_1(D_458)
      | ~ m1_subset_1(D_458,k3_zfmisc_1(A_455,B_456,C_457))
      | k1_xboole_0 = C_457
      | k1_xboole_0 = B_456
      | k1_xboole_0 = A_455 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2835,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_2831])).

tff(c_2838,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2835])).

tff(c_2744,plain,(
    ! [A_433,B_434] :
      ( r2_hidden('#skF_1'(A_433,B_434),A_433)
      | r1_tarski(A_433,B_434) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2749,plain,(
    ! [A_433] : r1_tarski(A_433,A_433) ),
    inference(resolution,[status(thm)],[c_2744,c_4])).

tff(c_10,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2751,plain,(
    ! [B_436,A_437] :
      ( ~ r1_xboole_0(B_436,A_437)
      | ~ r1_tarski(B_436,A_437)
      | v1_xboole_0(B_436) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2756,plain,(
    ! [A_438] :
      ( ~ r1_tarski(A_438,k1_xboole_0)
      | v1_xboole_0(A_438) ) ),
    inference(resolution,[status(thm)],[c_10,c_2751])).

tff(c_2765,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2749,c_2756])).

tff(c_2840,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2838,c_2765])).

tff(c_2845,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2836,c_2840])).

tff(c_2847,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2835])).

tff(c_2955,plain,(
    ! [A_475,B_476,C_477,D_478] :
      ( k6_mcart_1(A_475,B_476,C_477,D_478) = k2_mcart_1(k1_mcart_1(D_478))
      | ~ m1_subset_1(D_478,k3_zfmisc_1(A_475,B_476,C_477))
      | k1_xboole_0 = C_477
      | k1_xboole_0 = B_476
      | k1_xboole_0 = A_475 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2958,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_2955])).

tff(c_2961,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_2847,c_2958])).

tff(c_3412,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2961])).

tff(c_3418,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3412,c_2765])).

tff(c_3423,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2837,c_3418])).

tff(c_3425,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2961])).

tff(c_45,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(A_39,B_40)
      | ~ m1_subset_1(A_39,k1_zfmisc_1(B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_55,plain,(
    r1_tarski('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_45])).

tff(c_34,plain,(
    r2_hidden('#skF_8',k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1796,plain,(
    ! [A_311,B_312,C_313] : k2_zfmisc_1(k2_zfmisc_1(A_311,B_312),C_313) = k3_zfmisc_1(A_311,B_312,C_313) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_22,plain,(
    ! [A_18,C_20,B_19] :
      ( r2_hidden(k2_mcart_1(A_18),C_20)
      | ~ r2_hidden(A_18,k2_zfmisc_1(B_19,C_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1930,plain,(
    ! [A_342,C_343,A_344,B_345] :
      ( r2_hidden(k2_mcart_1(A_342),C_343)
      | ~ r2_hidden(A_342,k3_zfmisc_1(A_344,B_345,C_343)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1796,c_22])).

tff(c_1937,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_34,c_1930])).

tff(c_1830,plain,(
    ! [C_320,B_321,A_322] :
      ( ~ v1_xboole_0(C_320)
      | ~ m1_subset_1(B_321,k1_zfmisc_1(C_320))
      | ~ r2_hidden(A_322,B_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1841,plain,(
    ! [A_322] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_322,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40,c_1830])).

tff(c_1850,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1841])).

tff(c_1842,plain,(
    ! [A_322] :
      ( ~ v1_xboole_0('#skF_2')
      | ~ r2_hidden(A_322,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_42,c_1830])).

tff(c_1844,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1842])).

tff(c_1845,plain,(
    ! [A_323,B_324,C_325,D_326] :
      ( k7_mcart_1(A_323,B_324,C_325,D_326) = k2_mcart_1(D_326)
      | ~ m1_subset_1(D_326,k3_zfmisc_1(A_323,B_324,C_325))
      | k1_xboole_0 = C_325
      | k1_xboole_0 = B_324
      | k1_xboole_0 = A_323 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1849,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_1845])).

tff(c_1944,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1849])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1767,plain,(
    ! [B_302,A_303] :
      ( ~ r1_xboole_0(B_302,A_303)
      | ~ r1_tarski(B_302,A_303)
      | v1_xboole_0(B_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1772,plain,(
    ! [A_304] :
      ( ~ r1_tarski(A_304,k1_xboole_0)
      | v1_xboole_0(A_304) ) ),
    inference(resolution,[status(thm)],[c_10,c_1767])).

tff(c_1777,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_1772])).

tff(c_1947,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1944,c_1777])).

tff(c_1952,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1844,c_1947])).

tff(c_1954,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1849])).

tff(c_1913,plain,(
    ! [A_337,B_338,C_339,D_340] :
      ( k6_mcart_1(A_337,B_338,C_339,D_340) = k2_mcart_1(k1_mcart_1(D_340))
      | ~ m1_subset_1(D_340,k3_zfmisc_1(A_337,B_338,C_339))
      | k1_xboole_0 = C_339
      | k1_xboole_0 = B_338
      | k1_xboole_0 = A_337 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1917,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_1913])).

tff(c_2018,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1954,c_1917])).

tff(c_2019,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2018])).

tff(c_2024,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2019,c_1777])).

tff(c_2029,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1850,c_2024])).

tff(c_2031,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2018])).

tff(c_1953,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_1849])).

tff(c_2086,plain,
    ( k1_xboole_0 = '#skF_4'
    | k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_2031,c_1953])).

tff(c_2087,plain,(
    k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_2086])).

tff(c_32,plain,
    ( ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7')
    | ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6')
    | ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_58,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_76,plain,(
    ! [A_48,B_49] :
      ( r2_hidden('#skF_1'(A_48,B_49),A_48)
      | r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_81,plain,(
    ! [A_48] : r1_tarski(A_48,A_48) ),
    inference(resolution,[status(thm)],[c_76,c_4])).

tff(c_96,plain,(
    ! [C_54,B_55,A_56] :
      ( ~ v1_xboole_0(C_54)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(C_54))
      | ~ r2_hidden(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_107,plain,(
    ! [A_56] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_56,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40,c_96])).

tff(c_110,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_108,plain,(
    ! [A_56] :
      ( ~ v1_xboole_0('#skF_2')
      | ~ r2_hidden(A_56,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_42,c_96])).

tff(c_116,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_197,plain,(
    ! [A_76,B_77,C_78,D_79] :
      ( k7_mcart_1(A_76,B_77,C_78,D_79) = k2_mcart_1(D_79)
      | ~ m1_subset_1(D_79,k3_zfmisc_1(A_76,B_77,C_78))
      | k1_xboole_0 = C_78
      | k1_xboole_0 = B_77
      | k1_xboole_0 = A_76 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_201,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_197])).

tff(c_277,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_201])).

tff(c_64,plain,(
    ! [B_43,A_44] :
      ( ~ r1_xboole_0(B_43,A_44)
      | ~ r1_tarski(B_43,A_44)
      | v1_xboole_0(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_70,plain,(
    ! [A_47] :
      ( ~ r1_tarski(A_47,k1_xboole_0)
      | v1_xboole_0(A_47) ) ),
    inference(resolution,[status(thm)],[c_10,c_64])).

tff(c_75,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_70])).

tff(c_280,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_75])).

tff(c_285,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_280])).

tff(c_287,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_201])).

tff(c_231,plain,(
    ! [A_85,B_86,C_87,D_88] :
      ( k6_mcart_1(A_85,B_86,C_87,D_88) = k2_mcart_1(k1_mcart_1(D_88))
      | ~ m1_subset_1(D_88,k3_zfmisc_1(A_85,B_86,C_87))
      | k1_xboole_0 = C_87
      | k1_xboole_0 = B_86
      | k1_xboole_0 = A_85 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_235,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_231])).

tff(c_351,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_287,c_235])).

tff(c_352,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_351])).

tff(c_358,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_75])).

tff(c_363,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_358])).

tff(c_365,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_351])).

tff(c_306,plain,(
    ! [A_96,B_97,C_98,D_99] :
      ( k5_mcart_1(A_96,B_97,C_98,D_99) = k1_mcart_1(k1_mcart_1(D_99))
      | ~ m1_subset_1(D_99,k3_zfmisc_1(A_96,B_97,C_98))
      | k1_xboole_0 = C_98
      | k1_xboole_0 = B_97
      | k1_xboole_0 = A_96 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_309,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_306])).

tff(c_312,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_287,c_309])).

tff(c_569,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_365,c_312])).

tff(c_570,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_569])).

tff(c_178,plain,(
    ! [A_73,B_74,C_75] : k2_zfmisc_1(k2_zfmisc_1(A_73,B_74),C_75) = k3_zfmisc_1(A_73,B_74,C_75) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_202,plain,(
    ! [A_80,C_81,A_82,B_83] :
      ( r2_hidden(k2_mcart_1(A_80),C_81)
      | ~ r2_hidden(A_80,k3_zfmisc_1(A_82,B_83,C_81)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_22])).

tff(c_209,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_34,c_202])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_236,plain,(
    ! [B_89] :
      ( r2_hidden(k2_mcart_1('#skF_8'),B_89)
      | ~ r1_tarski('#skF_7',B_89) ) ),
    inference(resolution,[status(thm)],[c_209,c_2])).

tff(c_313,plain,(
    ! [B_100,B_101] :
      ( r2_hidden(k2_mcart_1('#skF_8'),B_100)
      | ~ r1_tarski(B_101,B_100)
      | ~ r1_tarski('#skF_7',B_101) ) ),
    inference(resolution,[status(thm)],[c_236,c_2])).

tff(c_323,plain,
    ( r2_hidden(k2_mcart_1('#skF_8'),'#skF_4')
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_55,c_313])).

tff(c_332,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_323])).

tff(c_377,plain,(
    ! [B_103] :
      ( r2_hidden(k2_mcart_1('#skF_8'),B_103)
      | ~ r1_tarski('#skF_4',B_103) ) ),
    inference(resolution,[status(thm)],[c_332,c_2])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_105,plain,(
    ! [B_11,A_56,A_10] :
      ( ~ v1_xboole_0(B_11)
      | ~ r2_hidden(A_56,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(resolution,[status(thm)],[c_16,c_96])).

tff(c_406,plain,(
    ! [B_104,B_105] :
      ( ~ v1_xboole_0(B_104)
      | ~ r1_tarski(B_105,B_104)
      | ~ r1_tarski('#skF_4',B_105) ) ),
    inference(resolution,[status(thm)],[c_377,c_105])).

tff(c_424,plain,(
    ! [A_6] :
      ( ~ v1_xboole_0(A_6)
      | ~ r1_tarski('#skF_4',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_406])).

tff(c_425,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_424])).

tff(c_572,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_570,c_425])).

tff(c_585,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_572])).

tff(c_586,plain,(
    k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_569])).

tff(c_24,plain,(
    ! [A_18,B_19,C_20] :
      ( r2_hidden(k1_mcart_1(A_18),B_19)
      | ~ r2_hidden(A_18,k2_zfmisc_1(B_19,C_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_599,plain,(
    ! [A_131,A_132,B_133,C_134] :
      ( r2_hidden(k1_mcart_1(A_131),k2_zfmisc_1(A_132,B_133))
      | ~ r2_hidden(A_131,k3_zfmisc_1(A_132,B_133,C_134)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_24])).

tff(c_621,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_34,c_599])).

tff(c_623,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_621,c_24])).

tff(c_631,plain,(
    r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_623])).

tff(c_633,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_631])).

tff(c_634,plain,(
    ! [A_6] : ~ v1_xboole_0(A_6) ),
    inference(splitRight,[status(thm)],[c_424])).

tff(c_639,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_634,c_75])).

tff(c_640,plain,(
    ! [A_56] : ~ r2_hidden(A_56,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_717,plain,(
    ! [A_150,B_151,C_152] : k2_zfmisc_1(k2_zfmisc_1(A_150,B_151),C_152) = k3_zfmisc_1(A_150,B_151,C_152) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1131,plain,(
    ! [A_206,A_207,B_208,C_209] :
      ( r2_hidden(k1_mcart_1(A_206),k2_zfmisc_1(A_207,B_208))
      | ~ r2_hidden(A_206,k3_zfmisc_1(A_207,B_208,C_209)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_717,c_24])).

tff(c_1150,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_34,c_1131])).

tff(c_1152,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_1150,c_24])).

tff(c_1162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_640,c_1152])).

tff(c_1163,plain,(
    ! [A_56] : ~ r2_hidden(A_56,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_1241,plain,(
    ! [A_225,B_226,C_227] : k2_zfmisc_1(k2_zfmisc_1(A_225,B_226),C_227) = k3_zfmisc_1(A_225,B_226,C_227) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1723,plain,(
    ! [A_294,A_295,B_296,C_297] :
      ( r2_hidden(k1_mcart_1(A_294),k2_zfmisc_1(A_295,B_296))
      | ~ r2_hidden(A_294,k3_zfmisc_1(A_295,B_296,C_297)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1241,c_24])).

tff(c_1745,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_34,c_1723])).

tff(c_1747,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_1745,c_22])).

tff(c_1757,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1163,c_1747])).

tff(c_1758,plain,
    ( ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6')
    | ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1766,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1758])).

tff(c_2088,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2087,c_1766])).

tff(c_2091,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1937,c_2088])).

tff(c_2092,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2086])).

tff(c_1977,plain,(
    ! [B_351] :
      ( r2_hidden(k2_mcart_1('#skF_8'),B_351)
      | ~ r1_tarski('#skF_7',B_351) ) ),
    inference(resolution,[status(thm)],[c_1937,c_2])).

tff(c_1839,plain,(
    ! [B_11,A_322,A_10] :
      ( ~ v1_xboole_0(B_11)
      | ~ r2_hidden(A_322,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(resolution,[status(thm)],[c_16,c_1830])).

tff(c_1996,plain,(
    ! [B_352,B_353] :
      ( ~ v1_xboole_0(B_352)
      | ~ r1_tarski(B_353,B_352)
      | ~ r1_tarski('#skF_7',B_353) ) ),
    inference(resolution,[status(thm)],[c_1977,c_1839])).

tff(c_2016,plain,(
    ! [A_6] :
      ( ~ v1_xboole_0(A_6)
      | ~ r1_tarski('#skF_7',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_1996])).

tff(c_2017,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2016])).

tff(c_2095,plain,(
    ~ r1_tarski('#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2092,c_2017])).

tff(c_2107,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_2095])).

tff(c_2108,plain,(
    ! [A_6] : ~ v1_xboole_0(A_6) ),
    inference(splitRight,[status(thm)],[c_2016])).

tff(c_2113,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2108,c_1777])).

tff(c_2114,plain,(
    ! [A_322] : ~ r2_hidden(A_322,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1841])).

tff(c_20,plain,(
    ! [A_15,B_16,C_17] : k2_zfmisc_1(k2_zfmisc_1(A_15,B_16),C_17) = k3_zfmisc_1(A_15,B_16,C_17) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1813,plain,(
    ! [A_314,B_315,C_316] :
      ( r2_hidden(k1_mcart_1(A_314),B_315)
      | ~ r2_hidden(A_314,k2_zfmisc_1(B_315,C_316)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2696,plain,(
    ! [A_429,A_430,B_431,C_432] :
      ( r2_hidden(k1_mcart_1(A_429),k2_zfmisc_1(A_430,B_431))
      | ~ r2_hidden(A_429,k3_zfmisc_1(A_430,B_431,C_432)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1813])).

tff(c_2722,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_34,c_2696])).

tff(c_2730,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_2722,c_22])).

tff(c_2737,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2114,c_2730])).

tff(c_2738,plain,(
    ! [A_322] : ~ r2_hidden(A_322,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_1842])).

tff(c_1759,plain,(
    r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_2741,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2738,c_1759])).

tff(c_2742,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1758])).

tff(c_3170,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2961])).

tff(c_3177,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3170,c_2765])).

tff(c_3182,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2837,c_3177])).

tff(c_3183,plain,
    ( k1_xboole_0 = '#skF_4'
    | k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_2961])).

tff(c_3189,plain,(
    k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_3183])).

tff(c_2793,plain,(
    ! [A_446,B_447,C_448] : k2_zfmisc_1(k2_zfmisc_1(A_446,B_447),C_448) = k3_zfmisc_1(A_446,B_447,C_448) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3347,plain,(
    ! [A_520,A_521,B_522,C_523] :
      ( r2_hidden(k1_mcart_1(A_520),k2_zfmisc_1(A_521,B_522))
      | ~ r2_hidden(A_520,k3_zfmisc_1(A_521,B_522,C_523)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2793,c_24])).

tff(c_3373,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_34,c_3347])).

tff(c_3377,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_3373,c_22])).

tff(c_3384,plain,(
    r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3189,c_3377])).

tff(c_3386,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2742,c_3384])).

tff(c_3387,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3183])).

tff(c_2846,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_2835])).

tff(c_2988,plain,(
    k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_2846])).

tff(c_2743,plain,(
    r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_1758])).

tff(c_2989,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2988,c_2743])).

tff(c_3000,plain,(
    ! [B_481] :
      ( r2_hidden(k2_mcart_1('#skF_8'),B_481)
      | ~ r1_tarski('#skF_7',B_481) ) ),
    inference(resolution,[status(thm)],[c_2989,c_2])).

tff(c_3059,plain,(
    ! [B_488,B_489] :
      ( r2_hidden(k2_mcart_1('#skF_8'),B_488)
      | ~ r1_tarski(B_489,B_488)
      | ~ r1_tarski('#skF_7',B_489) ) ),
    inference(resolution,[status(thm)],[c_3000,c_2])).

tff(c_3069,plain,
    ( r2_hidden(k2_mcart_1('#skF_8'),'#skF_4')
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_55,c_3059])).

tff(c_3078,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2749,c_3069])).

tff(c_3131,plain,(
    ! [B_494] :
      ( r2_hidden(k2_mcart_1('#skF_8'),B_494)
      | ~ r1_tarski('#skF_4',B_494) ) ),
    inference(resolution,[status(thm)],[c_3078,c_2])).

tff(c_2826,plain,(
    ! [B_11,A_454,A_10] :
      ( ~ v1_xboole_0(B_11)
      | ~ r2_hidden(A_454,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(resolution,[status(thm)],[c_16,c_2817])).

tff(c_3150,plain,(
    ! [B_495,B_496] :
      ( ~ v1_xboole_0(B_495)
      | ~ r1_tarski(B_496,B_495)
      | ~ r1_tarski('#skF_4',B_496) ) ),
    inference(resolution,[status(thm)],[c_3131,c_2826])).

tff(c_3168,plain,(
    ! [A_6] :
      ( ~ v1_xboole_0(A_6)
      | ~ r1_tarski('#skF_4',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_3150])).

tff(c_3169,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_3168])).

tff(c_3389,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3387,c_3169])).

tff(c_3403,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2749,c_3389])).

tff(c_3404,plain,(
    ! [A_6] : ~ v1_xboole_0(A_6) ),
    inference(splitRight,[status(thm)],[c_3168])).

tff(c_3409,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3404,c_2765])).

tff(c_3410,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2846])).

tff(c_3426,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_3425,c_3410])).

tff(c_3433,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3426,c_2765])).

tff(c_3438,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2830,c_3433])).

tff(c_3439,plain,(
    ! [A_454] : ~ r2_hidden(A_454,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_2828])).

tff(c_3969,plain,(
    ! [A_579,A_580,B_581,C_582] :
      ( r2_hidden(k1_mcart_1(A_579),k2_zfmisc_1(A_580,B_581))
      | ~ r2_hidden(A_579,k3_zfmisc_1(A_580,B_581,C_582)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2793,c_24])).

tff(c_3996,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_34,c_3969])).

tff(c_4004,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_3996,c_22])).

tff(c_4013,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3439,c_4004])).

tff(c_4014,plain,(
    ! [A_454] : ~ r2_hidden(A_454,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_2829])).

tff(c_4018,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4014,c_1759])).

tff(c_4019,plain,(
    ! [A_454] : ~ r2_hidden(A_454,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_2827])).

tff(c_4022,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4019,c_2743])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:33:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.68/1.91  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.02/1.93  
% 5.02/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.02/1.94  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1
% 5.02/1.94  
% 5.02/1.94  %Foreground sorts:
% 5.02/1.94  
% 5.02/1.94  
% 5.02/1.94  %Background operators:
% 5.02/1.94  
% 5.02/1.94  
% 5.02/1.94  %Foreground operators:
% 5.02/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.02/1.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.02/1.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.02/1.94  tff('#skF_7', type, '#skF_7': $i).
% 5.02/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.02/1.94  tff('#skF_5', type, '#skF_5': $i).
% 5.02/1.94  tff('#skF_6', type, '#skF_6': $i).
% 5.02/1.94  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.02/1.94  tff('#skF_2', type, '#skF_2': $i).
% 5.02/1.94  tff('#skF_3', type, '#skF_3': $i).
% 5.02/1.94  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 5.02/1.94  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 5.02/1.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.02/1.94  tff('#skF_8', type, '#skF_8': $i).
% 5.02/1.94  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 5.02/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.02/1.94  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 5.02/1.94  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.02/1.94  tff('#skF_4', type, '#skF_4': $i).
% 5.02/1.94  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 5.02/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.02/1.94  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 5.02/1.94  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.02/1.94  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.02/1.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.02/1.94  
% 5.02/1.97  tff(f_103, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (![F]: (m1_subset_1(F, k1_zfmisc_1(C)) => (![G]: (m1_subset_1(G, k3_zfmisc_1(A, B, C)) => (r2_hidden(G, k3_zfmisc_1(D, E, F)) => ((r2_hidden(k5_mcart_1(A, B, C, G), D) & r2_hidden(k6_mcart_1(A, B, C, G), E)) & r2_hidden(k7_mcart_1(A, B, C, G), F))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_mcart_1)).
% 5.02/1.97  tff(f_55, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 5.02/1.97  tff(f_83, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 5.02/1.97  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.02/1.97  tff(f_36, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.02/1.97  tff(f_44, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 5.02/1.97  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.02/1.97  tff(f_57, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 5.02/1.97  tff(f_63, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 5.02/1.97  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.02/1.97  tff(c_38, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.02/1.97  tff(c_2817, plain, (![C_452, B_453, A_454]: (~v1_xboole_0(C_452) | ~m1_subset_1(B_453, k1_zfmisc_1(C_452)) | ~r2_hidden(A_454, B_453))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.02/1.97  tff(c_2827, plain, (![A_454]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_454, '#skF_7'))), inference(resolution, [status(thm)], [c_38, c_2817])).
% 5.02/1.97  tff(c_2830, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_2827])).
% 5.02/1.97  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.02/1.97  tff(c_2828, plain, (![A_454]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_454, '#skF_6'))), inference(resolution, [status(thm)], [c_40, c_2817])).
% 5.02/1.97  tff(c_2837, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_2828])).
% 5.02/1.97  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.02/1.97  tff(c_2829, plain, (![A_454]: (~v1_xboole_0('#skF_2') | ~r2_hidden(A_454, '#skF_5'))), inference(resolution, [status(thm)], [c_42, c_2817])).
% 5.02/1.97  tff(c_2836, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_2829])).
% 5.02/1.97  tff(c_36, plain, (m1_subset_1('#skF_8', k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.02/1.97  tff(c_2831, plain, (![A_455, B_456, C_457, D_458]: (k7_mcart_1(A_455, B_456, C_457, D_458)=k2_mcart_1(D_458) | ~m1_subset_1(D_458, k3_zfmisc_1(A_455, B_456, C_457)) | k1_xboole_0=C_457 | k1_xboole_0=B_456 | k1_xboole_0=A_455)), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.02/1.97  tff(c_2835, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_2831])).
% 5.02/1.97  tff(c_2838, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_2835])).
% 5.02/1.97  tff(c_2744, plain, (![A_433, B_434]: (r2_hidden('#skF_1'(A_433, B_434), A_433) | r1_tarski(A_433, B_434))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.02/1.97  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.02/1.97  tff(c_2749, plain, (![A_433]: (r1_tarski(A_433, A_433))), inference(resolution, [status(thm)], [c_2744, c_4])).
% 5.02/1.97  tff(c_10, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.02/1.97  tff(c_2751, plain, (![B_436, A_437]: (~r1_xboole_0(B_436, A_437) | ~r1_tarski(B_436, A_437) | v1_xboole_0(B_436))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.02/1.97  tff(c_2756, plain, (![A_438]: (~r1_tarski(A_438, k1_xboole_0) | v1_xboole_0(A_438))), inference(resolution, [status(thm)], [c_10, c_2751])).
% 5.02/1.97  tff(c_2765, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_2749, c_2756])).
% 5.02/1.97  tff(c_2840, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2838, c_2765])).
% 5.02/1.97  tff(c_2845, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2836, c_2840])).
% 5.02/1.97  tff(c_2847, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_2835])).
% 5.02/1.97  tff(c_2955, plain, (![A_475, B_476, C_477, D_478]: (k6_mcart_1(A_475, B_476, C_477, D_478)=k2_mcart_1(k1_mcart_1(D_478)) | ~m1_subset_1(D_478, k3_zfmisc_1(A_475, B_476, C_477)) | k1_xboole_0=C_477 | k1_xboole_0=B_476 | k1_xboole_0=A_475)), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.02/1.97  tff(c_2958, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_2955])).
% 5.02/1.97  tff(c_2961, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_2847, c_2958])).
% 5.02/1.97  tff(c_3412, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2961])).
% 5.02/1.97  tff(c_3418, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3412, c_2765])).
% 5.02/1.97  tff(c_3423, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2837, c_3418])).
% 5.02/1.97  tff(c_3425, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_2961])).
% 5.02/1.97  tff(c_45, plain, (![A_39, B_40]: (r1_tarski(A_39, B_40) | ~m1_subset_1(A_39, k1_zfmisc_1(B_40)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.02/1.97  tff(c_55, plain, (r1_tarski('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_45])).
% 5.02/1.97  tff(c_34, plain, (r2_hidden('#skF_8', k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.02/1.97  tff(c_1796, plain, (![A_311, B_312, C_313]: (k2_zfmisc_1(k2_zfmisc_1(A_311, B_312), C_313)=k3_zfmisc_1(A_311, B_312, C_313))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.02/1.97  tff(c_22, plain, (![A_18, C_20, B_19]: (r2_hidden(k2_mcart_1(A_18), C_20) | ~r2_hidden(A_18, k2_zfmisc_1(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.02/1.97  tff(c_1930, plain, (![A_342, C_343, A_344, B_345]: (r2_hidden(k2_mcart_1(A_342), C_343) | ~r2_hidden(A_342, k3_zfmisc_1(A_344, B_345, C_343)))), inference(superposition, [status(thm), theory('equality')], [c_1796, c_22])).
% 5.02/1.97  tff(c_1937, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_34, c_1930])).
% 5.02/1.97  tff(c_1830, plain, (![C_320, B_321, A_322]: (~v1_xboole_0(C_320) | ~m1_subset_1(B_321, k1_zfmisc_1(C_320)) | ~r2_hidden(A_322, B_321))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.02/1.97  tff(c_1841, plain, (![A_322]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_322, '#skF_6'))), inference(resolution, [status(thm)], [c_40, c_1830])).
% 5.02/1.97  tff(c_1850, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_1841])).
% 5.02/1.97  tff(c_1842, plain, (![A_322]: (~v1_xboole_0('#skF_2') | ~r2_hidden(A_322, '#skF_5'))), inference(resolution, [status(thm)], [c_42, c_1830])).
% 5.02/1.97  tff(c_1844, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_1842])).
% 5.02/1.97  tff(c_1845, plain, (![A_323, B_324, C_325, D_326]: (k7_mcart_1(A_323, B_324, C_325, D_326)=k2_mcart_1(D_326) | ~m1_subset_1(D_326, k3_zfmisc_1(A_323, B_324, C_325)) | k1_xboole_0=C_325 | k1_xboole_0=B_324 | k1_xboole_0=A_323)), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.02/1.97  tff(c_1849, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_1845])).
% 5.02/1.97  tff(c_1944, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1849])).
% 5.02/1.97  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.02/1.97  tff(c_1767, plain, (![B_302, A_303]: (~r1_xboole_0(B_302, A_303) | ~r1_tarski(B_302, A_303) | v1_xboole_0(B_302))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.02/1.97  tff(c_1772, plain, (![A_304]: (~r1_tarski(A_304, k1_xboole_0) | v1_xboole_0(A_304))), inference(resolution, [status(thm)], [c_10, c_1767])).
% 5.02/1.97  tff(c_1777, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_1772])).
% 5.02/1.97  tff(c_1947, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1944, c_1777])).
% 5.02/1.97  tff(c_1952, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1844, c_1947])).
% 5.02/1.97  tff(c_1954, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_1849])).
% 5.02/1.97  tff(c_1913, plain, (![A_337, B_338, C_339, D_340]: (k6_mcart_1(A_337, B_338, C_339, D_340)=k2_mcart_1(k1_mcart_1(D_340)) | ~m1_subset_1(D_340, k3_zfmisc_1(A_337, B_338, C_339)) | k1_xboole_0=C_339 | k1_xboole_0=B_338 | k1_xboole_0=A_337)), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.02/1.97  tff(c_1917, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_1913])).
% 5.02/1.97  tff(c_2018, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1954, c_1917])).
% 5.02/1.97  tff(c_2019, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2018])).
% 5.02/1.97  tff(c_2024, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2019, c_1777])).
% 5.02/1.97  tff(c_2029, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1850, c_2024])).
% 5.02/1.97  tff(c_2031, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_2018])).
% 5.02/1.97  tff(c_1953, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4' | k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitRight, [status(thm)], [c_1849])).
% 5.02/1.97  tff(c_2086, plain, (k1_xboole_0='#skF_4' | k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_2031, c_1953])).
% 5.02/1.97  tff(c_2087, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitLeft, [status(thm)], [c_2086])).
% 5.02/1.97  tff(c_32, plain, (~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7') | ~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6') | ~r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.02/1.97  tff(c_58, plain, (~r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(splitLeft, [status(thm)], [c_32])).
% 5.02/1.97  tff(c_76, plain, (![A_48, B_49]: (r2_hidden('#skF_1'(A_48, B_49), A_48) | r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.02/1.97  tff(c_81, plain, (![A_48]: (r1_tarski(A_48, A_48))), inference(resolution, [status(thm)], [c_76, c_4])).
% 5.02/1.97  tff(c_96, plain, (![C_54, B_55, A_56]: (~v1_xboole_0(C_54) | ~m1_subset_1(B_55, k1_zfmisc_1(C_54)) | ~r2_hidden(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.02/1.97  tff(c_107, plain, (![A_56]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_56, '#skF_6'))), inference(resolution, [status(thm)], [c_40, c_96])).
% 5.02/1.97  tff(c_110, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_107])).
% 5.02/1.97  tff(c_108, plain, (![A_56]: (~v1_xboole_0('#skF_2') | ~r2_hidden(A_56, '#skF_5'))), inference(resolution, [status(thm)], [c_42, c_96])).
% 5.02/1.97  tff(c_116, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_108])).
% 5.02/1.97  tff(c_197, plain, (![A_76, B_77, C_78, D_79]: (k7_mcart_1(A_76, B_77, C_78, D_79)=k2_mcart_1(D_79) | ~m1_subset_1(D_79, k3_zfmisc_1(A_76, B_77, C_78)) | k1_xboole_0=C_78 | k1_xboole_0=B_77 | k1_xboole_0=A_76)), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.02/1.97  tff(c_201, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_197])).
% 5.02/1.97  tff(c_277, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_201])).
% 5.02/1.97  tff(c_64, plain, (![B_43, A_44]: (~r1_xboole_0(B_43, A_44) | ~r1_tarski(B_43, A_44) | v1_xboole_0(B_43))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.02/1.97  tff(c_70, plain, (![A_47]: (~r1_tarski(A_47, k1_xboole_0) | v1_xboole_0(A_47))), inference(resolution, [status(thm)], [c_10, c_64])).
% 5.02/1.97  tff(c_75, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_70])).
% 5.02/1.97  tff(c_280, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_277, c_75])).
% 5.02/1.97  tff(c_285, plain, $false, inference(negUnitSimplification, [status(thm)], [c_116, c_280])).
% 5.02/1.97  tff(c_287, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_201])).
% 5.02/1.97  tff(c_231, plain, (![A_85, B_86, C_87, D_88]: (k6_mcart_1(A_85, B_86, C_87, D_88)=k2_mcart_1(k1_mcart_1(D_88)) | ~m1_subset_1(D_88, k3_zfmisc_1(A_85, B_86, C_87)) | k1_xboole_0=C_87 | k1_xboole_0=B_86 | k1_xboole_0=A_85)), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.02/1.97  tff(c_235, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_231])).
% 5.02/1.97  tff(c_351, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_287, c_235])).
% 5.02/1.97  tff(c_352, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_351])).
% 5.02/1.97  tff(c_358, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_352, c_75])).
% 5.02/1.97  tff(c_363, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_358])).
% 5.02/1.97  tff(c_365, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_351])).
% 5.02/1.97  tff(c_306, plain, (![A_96, B_97, C_98, D_99]: (k5_mcart_1(A_96, B_97, C_98, D_99)=k1_mcart_1(k1_mcart_1(D_99)) | ~m1_subset_1(D_99, k3_zfmisc_1(A_96, B_97, C_98)) | k1_xboole_0=C_98 | k1_xboole_0=B_97 | k1_xboole_0=A_96)), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.02/1.97  tff(c_309, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_306])).
% 5.02/1.97  tff(c_312, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_287, c_309])).
% 5.02/1.97  tff(c_569, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_365, c_312])).
% 5.02/1.97  tff(c_570, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_569])).
% 5.02/1.97  tff(c_178, plain, (![A_73, B_74, C_75]: (k2_zfmisc_1(k2_zfmisc_1(A_73, B_74), C_75)=k3_zfmisc_1(A_73, B_74, C_75))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.02/1.97  tff(c_202, plain, (![A_80, C_81, A_82, B_83]: (r2_hidden(k2_mcart_1(A_80), C_81) | ~r2_hidden(A_80, k3_zfmisc_1(A_82, B_83, C_81)))), inference(superposition, [status(thm), theory('equality')], [c_178, c_22])).
% 5.02/1.97  tff(c_209, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_34, c_202])).
% 5.02/1.97  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.02/1.97  tff(c_236, plain, (![B_89]: (r2_hidden(k2_mcart_1('#skF_8'), B_89) | ~r1_tarski('#skF_7', B_89))), inference(resolution, [status(thm)], [c_209, c_2])).
% 5.02/1.97  tff(c_313, plain, (![B_100, B_101]: (r2_hidden(k2_mcart_1('#skF_8'), B_100) | ~r1_tarski(B_101, B_100) | ~r1_tarski('#skF_7', B_101))), inference(resolution, [status(thm)], [c_236, c_2])).
% 5.02/1.97  tff(c_323, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_4') | ~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_55, c_313])).
% 5.02/1.97  tff(c_332, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_323])).
% 5.02/1.97  tff(c_377, plain, (![B_103]: (r2_hidden(k2_mcart_1('#skF_8'), B_103) | ~r1_tarski('#skF_4', B_103))), inference(resolution, [status(thm)], [c_332, c_2])).
% 5.02/1.97  tff(c_16, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.02/1.97  tff(c_105, plain, (![B_11, A_56, A_10]: (~v1_xboole_0(B_11) | ~r2_hidden(A_56, A_10) | ~r1_tarski(A_10, B_11))), inference(resolution, [status(thm)], [c_16, c_96])).
% 5.02/1.97  tff(c_406, plain, (![B_104, B_105]: (~v1_xboole_0(B_104) | ~r1_tarski(B_105, B_104) | ~r1_tarski('#skF_4', B_105))), inference(resolution, [status(thm)], [c_377, c_105])).
% 5.02/1.97  tff(c_424, plain, (![A_6]: (~v1_xboole_0(A_6) | ~r1_tarski('#skF_4', k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_406])).
% 5.02/1.97  tff(c_425, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_424])).
% 5.02/1.97  tff(c_572, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_570, c_425])).
% 5.02/1.97  tff(c_585, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81, c_572])).
% 5.02/1.97  tff(c_586, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_569])).
% 5.02/1.97  tff(c_24, plain, (![A_18, B_19, C_20]: (r2_hidden(k1_mcart_1(A_18), B_19) | ~r2_hidden(A_18, k2_zfmisc_1(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.02/1.97  tff(c_599, plain, (![A_131, A_132, B_133, C_134]: (r2_hidden(k1_mcart_1(A_131), k2_zfmisc_1(A_132, B_133)) | ~r2_hidden(A_131, k3_zfmisc_1(A_132, B_133, C_134)))), inference(superposition, [status(thm), theory('equality')], [c_178, c_24])).
% 5.02/1.97  tff(c_621, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_34, c_599])).
% 5.02/1.97  tff(c_623, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')), '#skF_5')), inference(resolution, [status(thm)], [c_621, c_24])).
% 5.02/1.97  tff(c_631, plain, (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_586, c_623])).
% 5.02/1.97  tff(c_633, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_631])).
% 5.02/1.97  tff(c_634, plain, (![A_6]: (~v1_xboole_0(A_6))), inference(splitRight, [status(thm)], [c_424])).
% 5.02/1.97  tff(c_639, plain, $false, inference(negUnitSimplification, [status(thm)], [c_634, c_75])).
% 5.02/1.97  tff(c_640, plain, (![A_56]: (~r2_hidden(A_56, '#skF_5'))), inference(splitRight, [status(thm)], [c_108])).
% 5.02/1.97  tff(c_717, plain, (![A_150, B_151, C_152]: (k2_zfmisc_1(k2_zfmisc_1(A_150, B_151), C_152)=k3_zfmisc_1(A_150, B_151, C_152))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.02/1.97  tff(c_1131, plain, (![A_206, A_207, B_208, C_209]: (r2_hidden(k1_mcart_1(A_206), k2_zfmisc_1(A_207, B_208)) | ~r2_hidden(A_206, k3_zfmisc_1(A_207, B_208, C_209)))), inference(superposition, [status(thm), theory('equality')], [c_717, c_24])).
% 5.02/1.97  tff(c_1150, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_34, c_1131])).
% 5.02/1.97  tff(c_1152, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')), '#skF_5')), inference(resolution, [status(thm)], [c_1150, c_24])).
% 5.02/1.97  tff(c_1162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_640, c_1152])).
% 5.02/1.97  tff(c_1163, plain, (![A_56]: (~r2_hidden(A_56, '#skF_6'))), inference(splitRight, [status(thm)], [c_107])).
% 5.02/1.97  tff(c_1241, plain, (![A_225, B_226, C_227]: (k2_zfmisc_1(k2_zfmisc_1(A_225, B_226), C_227)=k3_zfmisc_1(A_225, B_226, C_227))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.02/1.97  tff(c_1723, plain, (![A_294, A_295, B_296, C_297]: (r2_hidden(k1_mcart_1(A_294), k2_zfmisc_1(A_295, B_296)) | ~r2_hidden(A_294, k3_zfmisc_1(A_295, B_296, C_297)))), inference(superposition, [status(thm), theory('equality')], [c_1241, c_24])).
% 5.02/1.97  tff(c_1745, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_34, c_1723])).
% 5.02/1.97  tff(c_1747, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_6')), inference(resolution, [status(thm)], [c_1745, c_22])).
% 5.02/1.97  tff(c_1757, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1163, c_1747])).
% 5.02/1.97  tff(c_1758, plain, (~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6') | ~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_32])).
% 5.02/1.97  tff(c_1766, plain, (~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_1758])).
% 5.02/1.97  tff(c_2088, plain, (~r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2087, c_1766])).
% 5.02/1.97  tff(c_2091, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1937, c_2088])).
% 5.02/1.97  tff(c_2092, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_2086])).
% 5.02/1.97  tff(c_1977, plain, (![B_351]: (r2_hidden(k2_mcart_1('#skF_8'), B_351) | ~r1_tarski('#skF_7', B_351))), inference(resolution, [status(thm)], [c_1937, c_2])).
% 5.02/1.97  tff(c_1839, plain, (![B_11, A_322, A_10]: (~v1_xboole_0(B_11) | ~r2_hidden(A_322, A_10) | ~r1_tarski(A_10, B_11))), inference(resolution, [status(thm)], [c_16, c_1830])).
% 5.02/1.97  tff(c_1996, plain, (![B_352, B_353]: (~v1_xboole_0(B_352) | ~r1_tarski(B_353, B_352) | ~r1_tarski('#skF_7', B_353))), inference(resolution, [status(thm)], [c_1977, c_1839])).
% 5.02/1.97  tff(c_2016, plain, (![A_6]: (~v1_xboole_0(A_6) | ~r1_tarski('#skF_7', k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_1996])).
% 5.02/1.97  tff(c_2017, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_2016])).
% 5.02/1.97  tff(c_2095, plain, (~r1_tarski('#skF_7', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2092, c_2017])).
% 5.02/1.97  tff(c_2107, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_2095])).
% 5.02/1.97  tff(c_2108, plain, (![A_6]: (~v1_xboole_0(A_6))), inference(splitRight, [status(thm)], [c_2016])).
% 5.02/1.97  tff(c_2113, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2108, c_1777])).
% 5.02/1.97  tff(c_2114, plain, (![A_322]: (~r2_hidden(A_322, '#skF_6'))), inference(splitRight, [status(thm)], [c_1841])).
% 5.02/1.97  tff(c_20, plain, (![A_15, B_16, C_17]: (k2_zfmisc_1(k2_zfmisc_1(A_15, B_16), C_17)=k3_zfmisc_1(A_15, B_16, C_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.02/1.97  tff(c_1813, plain, (![A_314, B_315, C_316]: (r2_hidden(k1_mcart_1(A_314), B_315) | ~r2_hidden(A_314, k2_zfmisc_1(B_315, C_316)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.02/1.97  tff(c_2696, plain, (![A_429, A_430, B_431, C_432]: (r2_hidden(k1_mcart_1(A_429), k2_zfmisc_1(A_430, B_431)) | ~r2_hidden(A_429, k3_zfmisc_1(A_430, B_431, C_432)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1813])).
% 5.02/1.97  tff(c_2722, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_34, c_2696])).
% 5.02/1.97  tff(c_2730, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_6')), inference(resolution, [status(thm)], [c_2722, c_22])).
% 5.02/1.97  tff(c_2737, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2114, c_2730])).
% 5.02/1.97  tff(c_2738, plain, (![A_322]: (~r2_hidden(A_322, '#skF_5'))), inference(splitRight, [status(thm)], [c_1842])).
% 5.02/1.97  tff(c_1759, plain, (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(splitRight, [status(thm)], [c_32])).
% 5.02/1.97  tff(c_2741, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2738, c_1759])).
% 5.02/1.97  tff(c_2742, plain, (~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6')), inference(splitRight, [status(thm)], [c_1758])).
% 5.02/1.97  tff(c_3170, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2961])).
% 5.02/1.97  tff(c_3177, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3170, c_2765])).
% 5.02/1.97  tff(c_3182, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2837, c_3177])).
% 5.02/1.97  tff(c_3183, plain, (k1_xboole_0='#skF_4' | k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_2961])).
% 5.02/1.97  tff(c_3189, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitLeft, [status(thm)], [c_3183])).
% 5.02/1.97  tff(c_2793, plain, (![A_446, B_447, C_448]: (k2_zfmisc_1(k2_zfmisc_1(A_446, B_447), C_448)=k3_zfmisc_1(A_446, B_447, C_448))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.02/1.97  tff(c_3347, plain, (![A_520, A_521, B_522, C_523]: (r2_hidden(k1_mcart_1(A_520), k2_zfmisc_1(A_521, B_522)) | ~r2_hidden(A_520, k3_zfmisc_1(A_521, B_522, C_523)))), inference(superposition, [status(thm), theory('equality')], [c_2793, c_24])).
% 5.02/1.97  tff(c_3373, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_34, c_3347])).
% 5.02/1.97  tff(c_3377, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_6')), inference(resolution, [status(thm)], [c_3373, c_22])).
% 5.02/1.97  tff(c_3384, plain, (r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3189, c_3377])).
% 5.02/1.97  tff(c_3386, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2742, c_3384])).
% 5.02/1.97  tff(c_3387, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_3183])).
% 5.02/1.97  tff(c_2846, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4' | k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitRight, [status(thm)], [c_2835])).
% 5.02/1.97  tff(c_2988, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitLeft, [status(thm)], [c_2846])).
% 5.02/1.97  tff(c_2743, plain, (r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_1758])).
% 5.02/1.97  tff(c_2989, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2988, c_2743])).
% 5.02/1.97  tff(c_3000, plain, (![B_481]: (r2_hidden(k2_mcart_1('#skF_8'), B_481) | ~r1_tarski('#skF_7', B_481))), inference(resolution, [status(thm)], [c_2989, c_2])).
% 5.02/1.97  tff(c_3059, plain, (![B_488, B_489]: (r2_hidden(k2_mcart_1('#skF_8'), B_488) | ~r1_tarski(B_489, B_488) | ~r1_tarski('#skF_7', B_489))), inference(resolution, [status(thm)], [c_3000, c_2])).
% 5.02/1.97  tff(c_3069, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_4') | ~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_55, c_3059])).
% 5.02/1.97  tff(c_3078, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2749, c_3069])).
% 5.02/1.97  tff(c_3131, plain, (![B_494]: (r2_hidden(k2_mcart_1('#skF_8'), B_494) | ~r1_tarski('#skF_4', B_494))), inference(resolution, [status(thm)], [c_3078, c_2])).
% 5.02/1.97  tff(c_2826, plain, (![B_11, A_454, A_10]: (~v1_xboole_0(B_11) | ~r2_hidden(A_454, A_10) | ~r1_tarski(A_10, B_11))), inference(resolution, [status(thm)], [c_16, c_2817])).
% 5.02/1.97  tff(c_3150, plain, (![B_495, B_496]: (~v1_xboole_0(B_495) | ~r1_tarski(B_496, B_495) | ~r1_tarski('#skF_4', B_496))), inference(resolution, [status(thm)], [c_3131, c_2826])).
% 5.02/1.97  tff(c_3168, plain, (![A_6]: (~v1_xboole_0(A_6) | ~r1_tarski('#skF_4', k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_3150])).
% 5.02/1.97  tff(c_3169, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_3168])).
% 5.02/1.97  tff(c_3389, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3387, c_3169])).
% 5.02/1.97  tff(c_3403, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2749, c_3389])).
% 5.02/1.97  tff(c_3404, plain, (![A_6]: (~v1_xboole_0(A_6))), inference(splitRight, [status(thm)], [c_3168])).
% 5.02/1.97  tff(c_3409, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3404, c_2765])).
% 5.02/1.97  tff(c_3410, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_2846])).
% 5.02/1.97  tff(c_3426, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_3425, c_3410])).
% 5.02/1.97  tff(c_3433, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3426, c_2765])).
% 5.02/1.97  tff(c_3438, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2830, c_3433])).
% 5.02/1.97  tff(c_3439, plain, (![A_454]: (~r2_hidden(A_454, '#skF_6'))), inference(splitRight, [status(thm)], [c_2828])).
% 5.02/1.97  tff(c_3969, plain, (![A_579, A_580, B_581, C_582]: (r2_hidden(k1_mcart_1(A_579), k2_zfmisc_1(A_580, B_581)) | ~r2_hidden(A_579, k3_zfmisc_1(A_580, B_581, C_582)))), inference(superposition, [status(thm), theory('equality')], [c_2793, c_24])).
% 5.02/1.97  tff(c_3996, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_34, c_3969])).
% 5.02/1.97  tff(c_4004, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_6')), inference(resolution, [status(thm)], [c_3996, c_22])).
% 5.02/1.97  tff(c_4013, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3439, c_4004])).
% 5.02/1.97  tff(c_4014, plain, (![A_454]: (~r2_hidden(A_454, '#skF_5'))), inference(splitRight, [status(thm)], [c_2829])).
% 5.02/1.97  tff(c_4018, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4014, c_1759])).
% 5.02/1.97  tff(c_4019, plain, (![A_454]: (~r2_hidden(A_454, '#skF_7'))), inference(splitRight, [status(thm)], [c_2827])).
% 5.02/1.97  tff(c_4022, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4019, c_2743])).
% 5.02/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.02/1.97  
% 5.02/1.97  Inference rules
% 5.02/1.97  ----------------------
% 5.02/1.97  #Ref     : 0
% 5.02/1.97  #Sup     : 912
% 5.02/1.97  #Fact    : 0
% 5.02/1.97  #Define  : 0
% 5.02/1.97  #Split   : 74
% 5.02/1.97  #Chain   : 0
% 5.02/1.97  #Close   : 0
% 5.02/1.97  
% 5.02/1.97  Ordering : KBO
% 5.02/1.97  
% 5.02/1.97  Simplification rules
% 5.02/1.97  ----------------------
% 5.02/1.97  #Subsume      : 477
% 5.02/1.97  #Demod        : 399
% 5.02/1.97  #Tautology    : 152
% 5.02/1.97  #SimpNegUnit  : 64
% 5.02/1.97  #BackRed      : 195
% 5.02/1.97  
% 5.02/1.97  #Partial instantiations: 0
% 5.02/1.97  #Strategies tried      : 1
% 5.02/1.97  
% 5.02/1.97  Timing (in seconds)
% 5.02/1.97  ----------------------
% 5.02/1.97  Preprocessing        : 0.32
% 5.02/1.97  Parsing              : 0.17
% 5.02/1.97  CNF conversion       : 0.02
% 5.02/1.97  Main loop            : 0.85
% 5.02/1.97  Inferencing          : 0.31
% 5.02/1.97  Reduction            : 0.27
% 5.02/1.97  Demodulation         : 0.18
% 5.02/1.97  BG Simplification    : 0.03
% 5.02/1.97  Subsumption          : 0.16
% 5.02/1.97  Abstraction          : 0.04
% 5.02/1.97  MUC search           : 0.00
% 5.02/1.97  Cooper               : 0.00
% 5.02/1.97  Total                : 1.23
% 5.02/1.97  Index Insertion      : 0.00
% 5.02/1.97  Index Deletion       : 0.00
% 5.02/1.97  Index Matching       : 0.00
% 5.02/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
