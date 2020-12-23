%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:12 EST 2020

% Result     : Theorem 4.72s
% Output     : CNFRefutation 4.72s
% Verified   : 
% Statistics : Number of formulae       :  207 ( 704 expanded)
%              Number of leaves         :   35 ( 240 expanded)
%              Depth                    :   13
%              Number of atoms          :  332 (1845 expanded)
%              Number of equality atoms :   93 ( 399 expanded)
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

tff(f_109,negated_conjecture,(
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

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_63,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_89,axiom,(
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
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ~ ( r1_tarski(C,A)
          & r1_tarski(C,B)
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1816,plain,(
    ! [A_320,B_321] :
      ( r1_tarski(A_320,B_321)
      | ~ m1_subset_1(A_320,k1_zfmisc_1(B_321)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1826,plain,(
    r1_tarski('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_1816])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1847,plain,(
    ! [C_332,B_333,A_334] :
      ( ~ v1_xboole_0(C_332)
      | ~ m1_subset_1(B_333,k1_zfmisc_1(C_332))
      | ~ r2_hidden(A_334,B_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1858,plain,(
    ! [A_334] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_334,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_42,c_1847])).

tff(c_1861,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1858])).

tff(c_36,plain,(
    r2_hidden('#skF_8',k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1873,plain,(
    ! [A_338,B_339,C_340] : k2_zfmisc_1(k2_zfmisc_1(A_338,B_339),C_340) = k3_zfmisc_1(A_338,B_339,C_340) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_24,plain,(
    ! [A_21,C_23,B_22] :
      ( r2_hidden(k2_mcart_1(A_21),C_23)
      | ~ r2_hidden(A_21,k2_zfmisc_1(B_22,C_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2033,plain,(
    ! [A_363,C_364,A_365,B_366] :
      ( r2_hidden(k2_mcart_1(A_363),C_364)
      | ~ r2_hidden(A_363,k3_zfmisc_1(A_365,B_366,C_364)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1873,c_24])).

tff(c_2044,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_2033])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1828,plain,(
    r1_tarski('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_1816])).

tff(c_38,plain,(
    m1_subset_1('#skF_8',k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2107,plain,(
    ! [A_371,B_372,C_373,D_374] :
      ( k7_mcart_1(A_371,B_372,C_373,D_374) = k2_mcart_1(D_374)
      | ~ m1_subset_1(D_374,k3_zfmisc_1(A_371,B_372,C_373))
      | k1_xboole_0 = C_373
      | k1_xboole_0 = B_372
      | k1_xboole_0 = A_371 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2111,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_2107])).

tff(c_2143,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2111])).

tff(c_10,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_76,plain,(
    ! [A_51,B_52] :
      ( r2_hidden('#skF_1'(A_51,B_52),A_51)
      | r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_81,plain,(
    ! [A_51] : r1_tarski(A_51,A_51) ),
    inference(resolution,[status(thm)],[c_76,c_4])).

tff(c_34,plain,
    ( ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7')
    | ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6')
    | ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_56,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_83,plain,(
    ! [C_54,B_55,A_56] :
      ( ~ v1_xboole_0(C_54)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(C_54))
      | ~ r2_hidden(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_94,plain,(
    ! [A_56] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_56,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_42,c_83])).

tff(c_97,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_95,plain,(
    ! [A_56] :
      ( ~ v1_xboole_0('#skF_2')
      | ~ r2_hidden(A_56,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_44,c_83])).

tff(c_98,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_326,plain,(
    ! [A_98,B_99,C_100,D_101] :
      ( k7_mcart_1(A_98,B_99,C_100,D_101) = k2_mcart_1(D_101)
      | ~ m1_subset_1(D_101,k3_zfmisc_1(A_98,B_99,C_100))
      | k1_xboole_0 = C_100
      | k1_xboole_0 = B_99
      | k1_xboole_0 = A_98 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_330,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_326])).

tff(c_347,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_330])).

tff(c_12,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_256,plain,(
    ! [A_87,B_88,C_89] :
      ( ~ r1_xboole_0(A_87,B_88)
      | ~ r1_tarski(C_89,B_88)
      | ~ r1_tarski(C_89,A_87)
      | v1_xboole_0(C_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_267,plain,(
    ! [C_90,A_91] :
      ( ~ r1_tarski(C_90,k1_xboole_0)
      | ~ r1_tarski(C_90,A_91)
      | v1_xboole_0(C_90) ) ),
    inference(resolution,[status(thm)],[c_12,c_256])).

tff(c_273,plain,(
    ! [A_91] :
      ( ~ r1_tarski(k1_xboole_0,A_91)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_81,c_267])).

tff(c_280,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_273])).

tff(c_349,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_280])).

tff(c_356,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_349])).

tff(c_358,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_330])).

tff(c_451,plain,(
    ! [A_114,B_115,C_116,D_117] :
      ( k5_mcart_1(A_114,B_115,C_116,D_117) = k1_mcart_1(k1_mcart_1(D_117))
      | ~ m1_subset_1(D_117,k3_zfmisc_1(A_114,B_115,C_116))
      | k1_xboole_0 = C_116
      | k1_xboole_0 = B_115
      | k1_xboole_0 = A_114 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_454,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_451])).

tff(c_457,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_358,c_454])).

tff(c_470,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_457])).

tff(c_476,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_280])).

tff(c_483,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_476])).

tff(c_484,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_457])).

tff(c_486,plain,(
    k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_484])).

tff(c_22,plain,(
    ! [A_18,B_19,C_20] : k2_zfmisc_1(k2_zfmisc_1(A_18,B_19),C_20) = k3_zfmisc_1(A_18,B_19,C_20) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_160,plain,(
    ! [A_72,B_73,C_74] :
      ( r2_hidden(k1_mcart_1(A_72),B_73)
      | ~ r2_hidden(A_72,k2_zfmisc_1(B_73,C_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_515,plain,(
    ! [A_123,A_124,B_125,C_126] :
      ( r2_hidden(k1_mcart_1(A_123),k2_zfmisc_1(A_124,B_125))
      | ~ r2_hidden(A_123,k3_zfmisc_1(A_124,B_125,C_126)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_160])).

tff(c_534,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_36,c_515])).

tff(c_26,plain,(
    ! [A_21,B_22,C_23] :
      ( r2_hidden(k1_mcart_1(A_21),B_22)
      | ~ r2_hidden(A_21,k2_zfmisc_1(B_22,C_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_538,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_534,c_26])).

tff(c_545,plain,(
    r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_486,c_538])).

tff(c_547,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_545])).

tff(c_548,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_484])).

tff(c_57,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(A_45,B_46)
      | ~ m1_subset_1(A_45,k1_zfmisc_1(B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_67,plain,(
    r1_tarski('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_57])).

tff(c_153,plain,(
    ! [A_69,C_70,B_71] :
      ( r2_hidden(k2_mcart_1(A_69),C_70)
      | ~ r2_hidden(A_69,k2_zfmisc_1(B_71,C_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_186,plain,(
    ! [A_79,C_80,A_81,B_82] :
      ( r2_hidden(k2_mcart_1(A_79),C_80)
      | ~ r2_hidden(A_79,k3_zfmisc_1(A_81,B_82,C_80)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_153])).

tff(c_193,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_186])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_215,plain,(
    ! [B_84] :
      ( r2_hidden(k2_mcart_1('#skF_8'),B_84)
      | ~ r1_tarski('#skF_7',B_84) ) ),
    inference(resolution,[status(thm)],[c_193,c_2])).

tff(c_299,plain,(
    ! [B_96,B_97] :
      ( r2_hidden(k2_mcart_1('#skF_8'),B_96)
      | ~ r1_tarski(B_97,B_96)
      | ~ r1_tarski('#skF_7',B_97) ) ),
    inference(resolution,[status(thm)],[c_215,c_2])).

tff(c_309,plain,
    ( r2_hidden(k2_mcart_1('#skF_8'),'#skF_4')
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_67,c_299])).

tff(c_318,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_309])).

tff(c_364,plain,(
    ! [B_103] :
      ( r2_hidden(k2_mcart_1('#skF_8'),B_103)
      | ~ r1_tarski('#skF_4',B_103) ) ),
    inference(resolution,[status(thm)],[c_318,c_2])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_92,plain,(
    ! [B_14,A_56,A_13] :
      ( ~ v1_xboole_0(B_14)
      | ~ r2_hidden(A_56,A_13)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(resolution,[status(thm)],[c_18,c_83])).

tff(c_390,plain,(
    ! [B_108,B_109] :
      ( ~ v1_xboole_0(B_108)
      | ~ r1_tarski(B_109,B_108)
      | ~ r1_tarski('#skF_4',B_109) ) ),
    inference(resolution,[status(thm)],[c_364,c_92])).

tff(c_408,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(A_8)
      | ~ r1_tarski('#skF_4',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_390])).

tff(c_409,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_408])).

tff(c_552,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_548,c_409])).

tff(c_564,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_552])).

tff(c_565,plain,(
    ! [A_8] : ~ v1_xboole_0(A_8) ),
    inference(splitRight,[status(thm)],[c_408])).

tff(c_570,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_565,c_280])).

tff(c_571,plain,(
    ! [A_56] : ~ r2_hidden(A_56,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_633,plain,(
    ! [A_144,B_145,C_146] : k2_zfmisc_1(k2_zfmisc_1(A_144,B_145),C_146) = k3_zfmisc_1(A_144,B_145,C_146) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1148,plain,(
    ! [A_221,A_222,B_223,C_224] :
      ( r2_hidden(k1_mcart_1(A_221),k2_zfmisc_1(A_222,B_223))
      | ~ r2_hidden(A_221,k3_zfmisc_1(A_222,B_223,C_224)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_633,c_26])).

tff(c_1170,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_36,c_1148])).

tff(c_1176,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_1170,c_26])).

tff(c_1184,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_571,c_1176])).

tff(c_1185,plain,(
    ! [A_56] : ~ r2_hidden(A_56,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_1246,plain,(
    ! [A_242,B_243,C_244] : k2_zfmisc_1(k2_zfmisc_1(A_242,B_243),C_244) = k3_zfmisc_1(A_242,B_243,C_244) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1776,plain,(
    ! [A_316,A_317,B_318,C_319] :
      ( r2_hidden(k1_mcart_1(A_316),k2_zfmisc_1(A_317,B_318))
      | ~ r2_hidden(A_316,k3_zfmisc_1(A_317,B_318,C_319)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1246,c_26])).

tff(c_1798,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_36,c_1776])).

tff(c_1806,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_1798,c_24])).

tff(c_1813,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1185,c_1806])).

tff(c_1815,plain,(
    r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_1944,plain,(
    ! [C_351,B_352,A_353] :
      ( r2_hidden(C_351,B_352)
      | ~ r2_hidden(C_351,A_353)
      | ~ r1_tarski(A_353,B_352) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1991,plain,(
    ! [B_360] :
      ( r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),B_360)
      | ~ r1_tarski('#skF_5',B_360) ) ),
    inference(resolution,[status(thm)],[c_1815,c_1944])).

tff(c_1856,plain,(
    ! [B_14,A_334,A_13] :
      ( ~ v1_xboole_0(B_14)
      | ~ r2_hidden(A_334,A_13)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(resolution,[status(thm)],[c_18,c_1847])).

tff(c_2006,plain,(
    ! [B_361,B_362] :
      ( ~ v1_xboole_0(B_361)
      | ~ r1_tarski(B_362,B_361)
      | ~ r1_tarski('#skF_5',B_362) ) ),
    inference(resolution,[status(thm)],[c_1991,c_1856])).

tff(c_2026,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(A_8)
      | ~ r1_tarski('#skF_5',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_2006])).

tff(c_2027,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2026])).

tff(c_2146,plain,(
    ~ r1_tarski('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2143,c_2027])).

tff(c_2154,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1828,c_2146])).

tff(c_2155,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_2111])).

tff(c_2204,plain,(
    k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_2155])).

tff(c_1814,plain,
    ( ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6')
    | ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_2032,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1814])).

tff(c_2205,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2204,c_2032])).

tff(c_2208,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2044,c_2205])).

tff(c_2209,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2155])).

tff(c_2211,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2209])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1835,plain,(
    ! [A_326,B_327] :
      ( ~ r2_hidden('#skF_1'(A_326,B_327),B_327)
      | r1_tarski(A_326,B_327) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1840,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_1835])).

tff(c_1954,plain,(
    ! [A_354,B_355,C_356] :
      ( ~ r1_xboole_0(A_354,B_355)
      | ~ r1_tarski(C_356,B_355)
      | ~ r1_tarski(C_356,A_354)
      | v1_xboole_0(C_356) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1961,plain,(
    ! [C_357,A_358] :
      ( ~ r1_tarski(C_357,k1_xboole_0)
      | ~ r1_tarski(C_357,A_358)
      | v1_xboole_0(C_357) ) ),
    inference(resolution,[status(thm)],[c_12,c_1954])).

tff(c_1967,plain,(
    ! [A_358] :
      ( ~ r1_tarski(k1_xboole_0,A_358)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1840,c_1961])).

tff(c_1974,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1967])).

tff(c_2217,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2211,c_1974])).

tff(c_2223,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1861,c_2217])).

tff(c_2224,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2209])).

tff(c_2066,plain,(
    ! [B_368] :
      ( r2_hidden(k2_mcart_1('#skF_8'),B_368)
      | ~ r1_tarski('#skF_7',B_368) ) ),
    inference(resolution,[status(thm)],[c_2044,c_2])).

tff(c_2085,plain,(
    ! [B_369,B_370] :
      ( ~ v1_xboole_0(B_369)
      | ~ r1_tarski(B_370,B_369)
      | ~ r1_tarski('#skF_7',B_370) ) ),
    inference(resolution,[status(thm)],[c_2066,c_1856])).

tff(c_2105,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(A_8)
      | ~ r1_tarski('#skF_7',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_2085])).

tff(c_2106,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2105])).

tff(c_2229,plain,(
    ~ r1_tarski('#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2224,c_2106])).

tff(c_2239,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1826,c_2229])).

tff(c_2240,plain,(
    ! [A_8] : ~ v1_xboole_0(A_8) ),
    inference(splitRight,[status(thm)],[c_2105])).

tff(c_2250,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2240,c_1974])).

tff(c_2251,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1814])).

tff(c_2311,plain,(
    ! [A_393,B_394,C_395,D_396] :
      ( k7_mcart_1(A_393,B_394,C_395,D_396) = k2_mcart_1(D_396)
      | ~ m1_subset_1(D_396,k3_zfmisc_1(A_393,B_394,C_395))
      | k1_xboole_0 = C_395
      | k1_xboole_0 = B_394
      | k1_xboole_0 = A_393 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2315,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_2311])).

tff(c_2342,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2315])).

tff(c_2345,plain,(
    ~ r1_tarski('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2342,c_2027])).

tff(c_2353,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1828,c_2345])).

tff(c_2355,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2315])).

tff(c_2476,plain,(
    ! [A_412,B_413,C_414,D_415] :
      ( k5_mcart_1(A_412,B_413,C_414,D_415) = k1_mcart_1(k1_mcart_1(D_415))
      | ~ m1_subset_1(D_415,k3_zfmisc_1(A_412,B_413,C_414))
      | k1_xboole_0 = C_414
      | k1_xboole_0 = B_413
      | k1_xboole_0 = A_412 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2479,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_2476])).

tff(c_2482,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_2355,c_2479])).

tff(c_2589,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2482])).

tff(c_2597,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2589,c_1974])).

tff(c_2603,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1861,c_2597])).

tff(c_2605,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2482])).

tff(c_2403,plain,(
    ! [A_404,B_405,C_406,D_407] :
      ( k6_mcart_1(A_404,B_405,C_406,D_407) = k2_mcart_1(k1_mcart_1(D_407))
      | ~ m1_subset_1(D_407,k3_zfmisc_1(A_404,B_405,C_406))
      | k1_xboole_0 = C_406
      | k1_xboole_0 = B_405
      | k1_xboole_0 = A_404 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2406,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_2403])).

tff(c_2409,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_2355,c_2406])).

tff(c_2637,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_2605,c_2409])).

tff(c_2638,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2637])).

tff(c_2274,plain,(
    ! [A_388,C_389,A_390,B_391] :
      ( r2_hidden(k2_mcart_1(A_388),C_389)
      | ~ r2_hidden(A_388,k3_zfmisc_1(A_390,B_391,C_389)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1873,c_24])).

tff(c_2285,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_2274])).

tff(c_2292,plain,(
    ! [B_392] :
      ( r2_hidden(k2_mcart_1('#skF_8'),B_392)
      | ~ r1_tarski('#skF_7',B_392) ) ),
    inference(resolution,[status(thm)],[c_2285,c_2])).

tff(c_2382,plain,(
    ! [B_402,B_403] :
      ( r2_hidden(k2_mcart_1('#skF_8'),B_402)
      | ~ r1_tarski(B_403,B_402)
      | ~ r1_tarski('#skF_7',B_403) ) ),
    inference(resolution,[status(thm)],[c_2292,c_2])).

tff(c_2392,plain,
    ( r2_hidden(k2_mcart_1('#skF_8'),'#skF_4')
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_1826,c_2382])).

tff(c_2401,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1840,c_2392])).

tff(c_2437,plain,(
    ! [B_409] :
      ( r2_hidden(k2_mcart_1('#skF_8'),B_409)
      | ~ r1_tarski('#skF_4',B_409) ) ),
    inference(resolution,[status(thm)],[c_2401,c_2])).

tff(c_2456,plain,(
    ! [B_410,B_411] :
      ( ~ v1_xboole_0(B_410)
      | ~ r1_tarski(B_411,B_410)
      | ~ r1_tarski('#skF_4',B_411) ) ),
    inference(resolution,[status(thm)],[c_2437,c_1856])).

tff(c_2474,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(A_8)
      | ~ r1_tarski('#skF_4',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_2456])).

tff(c_2475,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2474])).

tff(c_2641,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2638,c_2475])).

tff(c_2655,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1840,c_2641])).

tff(c_2656,plain,(
    k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_2637])).

tff(c_1937,plain,(
    ! [A_348,B_349,C_350] :
      ( r2_hidden(k1_mcart_1(A_348),B_349)
      | ~ r2_hidden(A_348,k2_zfmisc_1(B_349,C_350)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2696,plain,(
    ! [A_443,A_444,B_445,C_446] :
      ( r2_hidden(k1_mcart_1(A_443),k2_zfmisc_1(A_444,B_445))
      | ~ r2_hidden(A_443,k3_zfmisc_1(A_444,B_445,C_446)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1937])).

tff(c_2722,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_36,c_2696])).

tff(c_2730,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_2722,c_24])).

tff(c_2736,plain,(
    r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2656,c_2730])).

tff(c_2738,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2251,c_2736])).

tff(c_2739,plain,(
    ! [A_8] : ~ v1_xboole_0(A_8) ),
    inference(splitRight,[status(thm)],[c_2474])).

tff(c_2745,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2739,c_1974])).

tff(c_2746,plain,(
    ! [A_8] : ~ v1_xboole_0(A_8) ),
    inference(splitRight,[status(thm)],[c_2026])).

tff(c_2751,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2746,c_1974])).

tff(c_2752,plain,(
    ! [A_334] : ~ r2_hidden(A_334,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1858])).

tff(c_2815,plain,(
    ! [A_461,B_462,C_463] : k2_zfmisc_1(k2_zfmisc_1(A_461,B_462),C_463) = k3_zfmisc_1(A_461,B_462,C_463) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3438,plain,(
    ! [A_539,A_540,B_541,C_542] :
      ( r2_hidden(k1_mcart_1(A_539),k2_zfmisc_1(A_540,B_541))
      | ~ r2_hidden(A_539,k3_zfmisc_1(A_540,B_541,C_542)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2815,c_26])).

tff(c_3464,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_36,c_3438])).

tff(c_3472,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_3464,c_24])).

tff(c_3479,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2752,c_3472])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:23:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.72/1.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.72/1.86  
% 4.72/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.72/1.87  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1
% 4.72/1.87  
% 4.72/1.87  %Foreground sorts:
% 4.72/1.87  
% 4.72/1.87  
% 4.72/1.87  %Background operators:
% 4.72/1.87  
% 4.72/1.87  
% 4.72/1.87  %Foreground operators:
% 4.72/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.72/1.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.72/1.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.72/1.87  tff('#skF_7', type, '#skF_7': $i).
% 4.72/1.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.72/1.87  tff('#skF_5', type, '#skF_5': $i).
% 4.72/1.87  tff('#skF_6', type, '#skF_6': $i).
% 4.72/1.87  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.72/1.87  tff('#skF_2', type, '#skF_2': $i).
% 4.72/1.87  tff('#skF_3', type, '#skF_3': $i).
% 4.72/1.87  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 4.72/1.87  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 4.72/1.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.72/1.87  tff('#skF_8', type, '#skF_8': $i).
% 4.72/1.87  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 4.72/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.72/1.87  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 4.72/1.87  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.72/1.87  tff('#skF_4', type, '#skF_4': $i).
% 4.72/1.87  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 4.72/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.72/1.87  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 4.72/1.87  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.72/1.87  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.72/1.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.72/1.87  
% 4.72/1.89  tff(f_109, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (![F]: (m1_subset_1(F, k1_zfmisc_1(C)) => (![G]: (m1_subset_1(G, k3_zfmisc_1(A, B, C)) => (r2_hidden(G, k3_zfmisc_1(D, E, F)) => ((r2_hidden(k5_mcart_1(A, B, C, G), D) & r2_hidden(k6_mcart_1(A, B, C, G), E)) & r2_hidden(k7_mcart_1(A, B, C, G), F))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_mcart_1)).
% 4.72/1.89  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.72/1.89  tff(f_61, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 4.72/1.89  tff(f_63, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 4.72/1.89  tff(f_69, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 4.72/1.89  tff(f_89, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 4.72/1.89  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.72/1.89  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.72/1.89  tff(f_40, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.72/1.89  tff(f_50, axiom, (![A, B, C]: (~v1_xboole_0(C) => ~((r1_tarski(C, A) & r1_tarski(C, B)) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_xboole_1)).
% 4.72/1.89  tff(c_40, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.72/1.89  tff(c_1816, plain, (![A_320, B_321]: (r1_tarski(A_320, B_321) | ~m1_subset_1(A_320, k1_zfmisc_1(B_321)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.72/1.89  tff(c_1826, plain, (r1_tarski('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_1816])).
% 4.72/1.89  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.72/1.89  tff(c_1847, plain, (![C_332, B_333, A_334]: (~v1_xboole_0(C_332) | ~m1_subset_1(B_333, k1_zfmisc_1(C_332)) | ~r2_hidden(A_334, B_333))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.72/1.89  tff(c_1858, plain, (![A_334]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_334, '#skF_6'))), inference(resolution, [status(thm)], [c_42, c_1847])).
% 4.72/1.89  tff(c_1861, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_1858])).
% 4.72/1.89  tff(c_36, plain, (r2_hidden('#skF_8', k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.72/1.89  tff(c_1873, plain, (![A_338, B_339, C_340]: (k2_zfmisc_1(k2_zfmisc_1(A_338, B_339), C_340)=k3_zfmisc_1(A_338, B_339, C_340))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.72/1.89  tff(c_24, plain, (![A_21, C_23, B_22]: (r2_hidden(k2_mcart_1(A_21), C_23) | ~r2_hidden(A_21, k2_zfmisc_1(B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.72/1.89  tff(c_2033, plain, (![A_363, C_364, A_365, B_366]: (r2_hidden(k2_mcart_1(A_363), C_364) | ~r2_hidden(A_363, k3_zfmisc_1(A_365, B_366, C_364)))), inference(superposition, [status(thm), theory('equality')], [c_1873, c_24])).
% 4.72/1.89  tff(c_2044, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_36, c_2033])).
% 4.72/1.89  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.72/1.89  tff(c_1828, plain, (r1_tarski('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_1816])).
% 4.72/1.89  tff(c_38, plain, (m1_subset_1('#skF_8', k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.72/1.89  tff(c_2107, plain, (![A_371, B_372, C_373, D_374]: (k7_mcart_1(A_371, B_372, C_373, D_374)=k2_mcart_1(D_374) | ~m1_subset_1(D_374, k3_zfmisc_1(A_371, B_372, C_373)) | k1_xboole_0=C_373 | k1_xboole_0=B_372 | k1_xboole_0=A_371)), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.72/1.89  tff(c_2111, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_38, c_2107])).
% 4.72/1.89  tff(c_2143, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_2111])).
% 4.72/1.89  tff(c_10, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.72/1.89  tff(c_76, plain, (![A_51, B_52]: (r2_hidden('#skF_1'(A_51, B_52), A_51) | r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.72/1.89  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.72/1.89  tff(c_81, plain, (![A_51]: (r1_tarski(A_51, A_51))), inference(resolution, [status(thm)], [c_76, c_4])).
% 4.72/1.89  tff(c_34, plain, (~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7') | ~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6') | ~r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.72/1.89  tff(c_56, plain, (~r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(splitLeft, [status(thm)], [c_34])).
% 4.72/1.89  tff(c_83, plain, (![C_54, B_55, A_56]: (~v1_xboole_0(C_54) | ~m1_subset_1(B_55, k1_zfmisc_1(C_54)) | ~r2_hidden(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.72/1.89  tff(c_94, plain, (![A_56]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_56, '#skF_6'))), inference(resolution, [status(thm)], [c_42, c_83])).
% 4.72/1.89  tff(c_97, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_94])).
% 4.72/1.89  tff(c_95, plain, (![A_56]: (~v1_xboole_0('#skF_2') | ~r2_hidden(A_56, '#skF_5'))), inference(resolution, [status(thm)], [c_44, c_83])).
% 4.72/1.89  tff(c_98, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_95])).
% 4.72/1.89  tff(c_326, plain, (![A_98, B_99, C_100, D_101]: (k7_mcart_1(A_98, B_99, C_100, D_101)=k2_mcart_1(D_101) | ~m1_subset_1(D_101, k3_zfmisc_1(A_98, B_99, C_100)) | k1_xboole_0=C_100 | k1_xboole_0=B_99 | k1_xboole_0=A_98)), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.72/1.89  tff(c_330, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_38, c_326])).
% 4.72/1.89  tff(c_347, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_330])).
% 4.72/1.89  tff(c_12, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.72/1.89  tff(c_256, plain, (![A_87, B_88, C_89]: (~r1_xboole_0(A_87, B_88) | ~r1_tarski(C_89, B_88) | ~r1_tarski(C_89, A_87) | v1_xboole_0(C_89))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.72/1.89  tff(c_267, plain, (![C_90, A_91]: (~r1_tarski(C_90, k1_xboole_0) | ~r1_tarski(C_90, A_91) | v1_xboole_0(C_90))), inference(resolution, [status(thm)], [c_12, c_256])).
% 4.72/1.89  tff(c_273, plain, (![A_91]: (~r1_tarski(k1_xboole_0, A_91) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_81, c_267])).
% 4.72/1.89  tff(c_280, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_273])).
% 4.72/1.89  tff(c_349, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_347, c_280])).
% 4.72/1.89  tff(c_356, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_349])).
% 4.72/1.89  tff(c_358, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_330])).
% 4.72/1.89  tff(c_451, plain, (![A_114, B_115, C_116, D_117]: (k5_mcart_1(A_114, B_115, C_116, D_117)=k1_mcart_1(k1_mcart_1(D_117)) | ~m1_subset_1(D_117, k3_zfmisc_1(A_114, B_115, C_116)) | k1_xboole_0=C_116 | k1_xboole_0=B_115 | k1_xboole_0=A_114)), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.72/1.89  tff(c_454, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_38, c_451])).
% 4.72/1.89  tff(c_457, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_358, c_454])).
% 4.72/1.89  tff(c_470, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_457])).
% 4.72/1.89  tff(c_476, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_470, c_280])).
% 4.72/1.89  tff(c_483, plain, $false, inference(negUnitSimplification, [status(thm)], [c_97, c_476])).
% 4.72/1.89  tff(c_484, plain, (k1_xboole_0='#skF_4' | k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_457])).
% 4.72/1.89  tff(c_486, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitLeft, [status(thm)], [c_484])).
% 4.72/1.89  tff(c_22, plain, (![A_18, B_19, C_20]: (k2_zfmisc_1(k2_zfmisc_1(A_18, B_19), C_20)=k3_zfmisc_1(A_18, B_19, C_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.72/1.89  tff(c_160, plain, (![A_72, B_73, C_74]: (r2_hidden(k1_mcart_1(A_72), B_73) | ~r2_hidden(A_72, k2_zfmisc_1(B_73, C_74)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.72/1.89  tff(c_515, plain, (![A_123, A_124, B_125, C_126]: (r2_hidden(k1_mcart_1(A_123), k2_zfmisc_1(A_124, B_125)) | ~r2_hidden(A_123, k3_zfmisc_1(A_124, B_125, C_126)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_160])).
% 4.72/1.89  tff(c_534, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_36, c_515])).
% 4.72/1.89  tff(c_26, plain, (![A_21, B_22, C_23]: (r2_hidden(k1_mcart_1(A_21), B_22) | ~r2_hidden(A_21, k2_zfmisc_1(B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.72/1.89  tff(c_538, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')), '#skF_5')), inference(resolution, [status(thm)], [c_534, c_26])).
% 4.72/1.89  tff(c_545, plain, (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_486, c_538])).
% 4.72/1.89  tff(c_547, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_545])).
% 4.72/1.89  tff(c_548, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_484])).
% 4.72/1.89  tff(c_57, plain, (![A_45, B_46]: (r1_tarski(A_45, B_46) | ~m1_subset_1(A_45, k1_zfmisc_1(B_46)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.72/1.89  tff(c_67, plain, (r1_tarski('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_57])).
% 4.72/1.89  tff(c_153, plain, (![A_69, C_70, B_71]: (r2_hidden(k2_mcart_1(A_69), C_70) | ~r2_hidden(A_69, k2_zfmisc_1(B_71, C_70)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.72/1.89  tff(c_186, plain, (![A_79, C_80, A_81, B_82]: (r2_hidden(k2_mcart_1(A_79), C_80) | ~r2_hidden(A_79, k3_zfmisc_1(A_81, B_82, C_80)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_153])).
% 4.72/1.89  tff(c_193, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_36, c_186])).
% 4.72/1.89  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.72/1.89  tff(c_215, plain, (![B_84]: (r2_hidden(k2_mcart_1('#skF_8'), B_84) | ~r1_tarski('#skF_7', B_84))), inference(resolution, [status(thm)], [c_193, c_2])).
% 4.72/1.89  tff(c_299, plain, (![B_96, B_97]: (r2_hidden(k2_mcart_1('#skF_8'), B_96) | ~r1_tarski(B_97, B_96) | ~r1_tarski('#skF_7', B_97))), inference(resolution, [status(thm)], [c_215, c_2])).
% 4.72/1.89  tff(c_309, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_4') | ~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_67, c_299])).
% 4.72/1.89  tff(c_318, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_309])).
% 4.72/1.89  tff(c_364, plain, (![B_103]: (r2_hidden(k2_mcart_1('#skF_8'), B_103) | ~r1_tarski('#skF_4', B_103))), inference(resolution, [status(thm)], [c_318, c_2])).
% 4.72/1.89  tff(c_18, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.72/1.89  tff(c_92, plain, (![B_14, A_56, A_13]: (~v1_xboole_0(B_14) | ~r2_hidden(A_56, A_13) | ~r1_tarski(A_13, B_14))), inference(resolution, [status(thm)], [c_18, c_83])).
% 4.72/1.89  tff(c_390, plain, (![B_108, B_109]: (~v1_xboole_0(B_108) | ~r1_tarski(B_109, B_108) | ~r1_tarski('#skF_4', B_109))), inference(resolution, [status(thm)], [c_364, c_92])).
% 4.72/1.89  tff(c_408, plain, (![A_8]: (~v1_xboole_0(A_8) | ~r1_tarski('#skF_4', k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_390])).
% 4.72/1.89  tff(c_409, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_408])).
% 4.72/1.89  tff(c_552, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_548, c_409])).
% 4.72/1.89  tff(c_564, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81, c_552])).
% 4.72/1.89  tff(c_565, plain, (![A_8]: (~v1_xboole_0(A_8))), inference(splitRight, [status(thm)], [c_408])).
% 4.72/1.89  tff(c_570, plain, $false, inference(negUnitSimplification, [status(thm)], [c_565, c_280])).
% 4.72/1.89  tff(c_571, plain, (![A_56]: (~r2_hidden(A_56, '#skF_5'))), inference(splitRight, [status(thm)], [c_95])).
% 4.72/1.89  tff(c_633, plain, (![A_144, B_145, C_146]: (k2_zfmisc_1(k2_zfmisc_1(A_144, B_145), C_146)=k3_zfmisc_1(A_144, B_145, C_146))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.72/1.89  tff(c_1148, plain, (![A_221, A_222, B_223, C_224]: (r2_hidden(k1_mcart_1(A_221), k2_zfmisc_1(A_222, B_223)) | ~r2_hidden(A_221, k3_zfmisc_1(A_222, B_223, C_224)))), inference(superposition, [status(thm), theory('equality')], [c_633, c_26])).
% 4.72/1.89  tff(c_1170, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_36, c_1148])).
% 4.72/1.89  tff(c_1176, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')), '#skF_5')), inference(resolution, [status(thm)], [c_1170, c_26])).
% 4.72/1.89  tff(c_1184, plain, $false, inference(negUnitSimplification, [status(thm)], [c_571, c_1176])).
% 4.72/1.89  tff(c_1185, plain, (![A_56]: (~r2_hidden(A_56, '#skF_6'))), inference(splitRight, [status(thm)], [c_94])).
% 4.72/1.89  tff(c_1246, plain, (![A_242, B_243, C_244]: (k2_zfmisc_1(k2_zfmisc_1(A_242, B_243), C_244)=k3_zfmisc_1(A_242, B_243, C_244))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.72/1.89  tff(c_1776, plain, (![A_316, A_317, B_318, C_319]: (r2_hidden(k1_mcart_1(A_316), k2_zfmisc_1(A_317, B_318)) | ~r2_hidden(A_316, k3_zfmisc_1(A_317, B_318, C_319)))), inference(superposition, [status(thm), theory('equality')], [c_1246, c_26])).
% 4.72/1.89  tff(c_1798, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_36, c_1776])).
% 4.72/1.89  tff(c_1806, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_6')), inference(resolution, [status(thm)], [c_1798, c_24])).
% 4.72/1.89  tff(c_1813, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1185, c_1806])).
% 4.72/1.89  tff(c_1815, plain, (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(splitRight, [status(thm)], [c_34])).
% 4.72/1.89  tff(c_1944, plain, (![C_351, B_352, A_353]: (r2_hidden(C_351, B_352) | ~r2_hidden(C_351, A_353) | ~r1_tarski(A_353, B_352))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.72/1.89  tff(c_1991, plain, (![B_360]: (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), B_360) | ~r1_tarski('#skF_5', B_360))), inference(resolution, [status(thm)], [c_1815, c_1944])).
% 4.72/1.89  tff(c_1856, plain, (![B_14, A_334, A_13]: (~v1_xboole_0(B_14) | ~r2_hidden(A_334, A_13) | ~r1_tarski(A_13, B_14))), inference(resolution, [status(thm)], [c_18, c_1847])).
% 4.72/1.89  tff(c_2006, plain, (![B_361, B_362]: (~v1_xboole_0(B_361) | ~r1_tarski(B_362, B_361) | ~r1_tarski('#skF_5', B_362))), inference(resolution, [status(thm)], [c_1991, c_1856])).
% 4.72/1.89  tff(c_2026, plain, (![A_8]: (~v1_xboole_0(A_8) | ~r1_tarski('#skF_5', k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_2006])).
% 4.72/1.89  tff(c_2027, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_2026])).
% 4.72/1.89  tff(c_2146, plain, (~r1_tarski('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2143, c_2027])).
% 4.72/1.89  tff(c_2154, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1828, c_2146])).
% 4.72/1.89  tff(c_2155, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4' | k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitRight, [status(thm)], [c_2111])).
% 4.72/1.89  tff(c_2204, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitLeft, [status(thm)], [c_2155])).
% 4.72/1.89  tff(c_1814, plain, (~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6') | ~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_34])).
% 4.72/1.89  tff(c_2032, plain, (~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_1814])).
% 4.72/1.89  tff(c_2205, plain, (~r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2204, c_2032])).
% 4.72/1.89  tff(c_2208, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2044, c_2205])).
% 4.72/1.89  tff(c_2209, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_2155])).
% 4.72/1.89  tff(c_2211, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2209])).
% 4.72/1.89  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.72/1.89  tff(c_1835, plain, (![A_326, B_327]: (~r2_hidden('#skF_1'(A_326, B_327), B_327) | r1_tarski(A_326, B_327))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.72/1.89  tff(c_1840, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_1835])).
% 4.72/1.89  tff(c_1954, plain, (![A_354, B_355, C_356]: (~r1_xboole_0(A_354, B_355) | ~r1_tarski(C_356, B_355) | ~r1_tarski(C_356, A_354) | v1_xboole_0(C_356))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.72/1.89  tff(c_1961, plain, (![C_357, A_358]: (~r1_tarski(C_357, k1_xboole_0) | ~r1_tarski(C_357, A_358) | v1_xboole_0(C_357))), inference(resolution, [status(thm)], [c_12, c_1954])).
% 4.72/1.89  tff(c_1967, plain, (![A_358]: (~r1_tarski(k1_xboole_0, A_358) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_1840, c_1961])).
% 4.72/1.89  tff(c_1974, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1967])).
% 4.72/1.89  tff(c_2217, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2211, c_1974])).
% 4.72/1.89  tff(c_2223, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1861, c_2217])).
% 4.72/1.89  tff(c_2224, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_2209])).
% 4.72/1.89  tff(c_2066, plain, (![B_368]: (r2_hidden(k2_mcart_1('#skF_8'), B_368) | ~r1_tarski('#skF_7', B_368))), inference(resolution, [status(thm)], [c_2044, c_2])).
% 4.72/1.89  tff(c_2085, plain, (![B_369, B_370]: (~v1_xboole_0(B_369) | ~r1_tarski(B_370, B_369) | ~r1_tarski('#skF_7', B_370))), inference(resolution, [status(thm)], [c_2066, c_1856])).
% 4.72/1.89  tff(c_2105, plain, (![A_8]: (~v1_xboole_0(A_8) | ~r1_tarski('#skF_7', k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_2085])).
% 4.72/1.89  tff(c_2106, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_2105])).
% 4.72/1.89  tff(c_2229, plain, (~r1_tarski('#skF_7', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2224, c_2106])).
% 4.72/1.89  tff(c_2239, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1826, c_2229])).
% 4.72/1.89  tff(c_2240, plain, (![A_8]: (~v1_xboole_0(A_8))), inference(splitRight, [status(thm)], [c_2105])).
% 4.72/1.89  tff(c_2250, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2240, c_1974])).
% 4.72/1.89  tff(c_2251, plain, (~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6')), inference(splitRight, [status(thm)], [c_1814])).
% 4.72/1.89  tff(c_2311, plain, (![A_393, B_394, C_395, D_396]: (k7_mcart_1(A_393, B_394, C_395, D_396)=k2_mcart_1(D_396) | ~m1_subset_1(D_396, k3_zfmisc_1(A_393, B_394, C_395)) | k1_xboole_0=C_395 | k1_xboole_0=B_394 | k1_xboole_0=A_393)), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.72/1.89  tff(c_2315, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_38, c_2311])).
% 4.72/1.89  tff(c_2342, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_2315])).
% 4.72/1.89  tff(c_2345, plain, (~r1_tarski('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2342, c_2027])).
% 4.72/1.89  tff(c_2353, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1828, c_2345])).
% 4.72/1.89  tff(c_2355, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_2315])).
% 4.72/1.89  tff(c_2476, plain, (![A_412, B_413, C_414, D_415]: (k5_mcart_1(A_412, B_413, C_414, D_415)=k1_mcart_1(k1_mcart_1(D_415)) | ~m1_subset_1(D_415, k3_zfmisc_1(A_412, B_413, C_414)) | k1_xboole_0=C_414 | k1_xboole_0=B_413 | k1_xboole_0=A_412)), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.72/1.89  tff(c_2479, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_38, c_2476])).
% 4.72/1.89  tff(c_2482, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_2355, c_2479])).
% 4.72/1.89  tff(c_2589, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2482])).
% 4.72/1.89  tff(c_2597, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2589, c_1974])).
% 4.72/1.89  tff(c_2603, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1861, c_2597])).
% 4.72/1.89  tff(c_2605, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_2482])).
% 4.72/1.89  tff(c_2403, plain, (![A_404, B_405, C_406, D_407]: (k6_mcart_1(A_404, B_405, C_406, D_407)=k2_mcart_1(k1_mcart_1(D_407)) | ~m1_subset_1(D_407, k3_zfmisc_1(A_404, B_405, C_406)) | k1_xboole_0=C_406 | k1_xboole_0=B_405 | k1_xboole_0=A_404)), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.72/1.89  tff(c_2406, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_38, c_2403])).
% 4.72/1.89  tff(c_2409, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_2355, c_2406])).
% 4.72/1.89  tff(c_2637, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_2605, c_2409])).
% 4.72/1.89  tff(c_2638, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_2637])).
% 4.72/1.89  tff(c_2274, plain, (![A_388, C_389, A_390, B_391]: (r2_hidden(k2_mcart_1(A_388), C_389) | ~r2_hidden(A_388, k3_zfmisc_1(A_390, B_391, C_389)))), inference(superposition, [status(thm), theory('equality')], [c_1873, c_24])).
% 4.72/1.89  tff(c_2285, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_36, c_2274])).
% 4.72/1.89  tff(c_2292, plain, (![B_392]: (r2_hidden(k2_mcart_1('#skF_8'), B_392) | ~r1_tarski('#skF_7', B_392))), inference(resolution, [status(thm)], [c_2285, c_2])).
% 4.72/1.89  tff(c_2382, plain, (![B_402, B_403]: (r2_hidden(k2_mcart_1('#skF_8'), B_402) | ~r1_tarski(B_403, B_402) | ~r1_tarski('#skF_7', B_403))), inference(resolution, [status(thm)], [c_2292, c_2])).
% 4.72/1.89  tff(c_2392, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_4') | ~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_1826, c_2382])).
% 4.72/1.89  tff(c_2401, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1840, c_2392])).
% 4.72/1.89  tff(c_2437, plain, (![B_409]: (r2_hidden(k2_mcart_1('#skF_8'), B_409) | ~r1_tarski('#skF_4', B_409))), inference(resolution, [status(thm)], [c_2401, c_2])).
% 4.72/1.89  tff(c_2456, plain, (![B_410, B_411]: (~v1_xboole_0(B_410) | ~r1_tarski(B_411, B_410) | ~r1_tarski('#skF_4', B_411))), inference(resolution, [status(thm)], [c_2437, c_1856])).
% 4.72/1.89  tff(c_2474, plain, (![A_8]: (~v1_xboole_0(A_8) | ~r1_tarski('#skF_4', k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_2456])).
% 4.72/1.89  tff(c_2475, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_2474])).
% 4.72/1.89  tff(c_2641, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2638, c_2475])).
% 4.72/1.89  tff(c_2655, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1840, c_2641])).
% 4.72/1.89  tff(c_2656, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_2637])).
% 4.72/1.89  tff(c_1937, plain, (![A_348, B_349, C_350]: (r2_hidden(k1_mcart_1(A_348), B_349) | ~r2_hidden(A_348, k2_zfmisc_1(B_349, C_350)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.72/1.89  tff(c_2696, plain, (![A_443, A_444, B_445, C_446]: (r2_hidden(k1_mcart_1(A_443), k2_zfmisc_1(A_444, B_445)) | ~r2_hidden(A_443, k3_zfmisc_1(A_444, B_445, C_446)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1937])).
% 4.72/1.89  tff(c_2722, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_36, c_2696])).
% 4.72/1.89  tff(c_2730, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_6')), inference(resolution, [status(thm)], [c_2722, c_24])).
% 4.72/1.89  tff(c_2736, plain, (r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2656, c_2730])).
% 4.72/1.89  tff(c_2738, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2251, c_2736])).
% 4.72/1.89  tff(c_2739, plain, (![A_8]: (~v1_xboole_0(A_8))), inference(splitRight, [status(thm)], [c_2474])).
% 4.72/1.89  tff(c_2745, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2739, c_1974])).
% 4.72/1.89  tff(c_2746, plain, (![A_8]: (~v1_xboole_0(A_8))), inference(splitRight, [status(thm)], [c_2026])).
% 4.72/1.89  tff(c_2751, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2746, c_1974])).
% 4.72/1.89  tff(c_2752, plain, (![A_334]: (~r2_hidden(A_334, '#skF_6'))), inference(splitRight, [status(thm)], [c_1858])).
% 4.72/1.89  tff(c_2815, plain, (![A_461, B_462, C_463]: (k2_zfmisc_1(k2_zfmisc_1(A_461, B_462), C_463)=k3_zfmisc_1(A_461, B_462, C_463))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.72/1.89  tff(c_3438, plain, (![A_539, A_540, B_541, C_542]: (r2_hidden(k1_mcart_1(A_539), k2_zfmisc_1(A_540, B_541)) | ~r2_hidden(A_539, k3_zfmisc_1(A_540, B_541, C_542)))), inference(superposition, [status(thm), theory('equality')], [c_2815, c_26])).
% 4.72/1.89  tff(c_3464, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_36, c_3438])).
% 4.72/1.89  tff(c_3472, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_6')), inference(resolution, [status(thm)], [c_3464, c_24])).
% 4.72/1.89  tff(c_3479, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2752, c_3472])).
% 4.72/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.72/1.89  
% 4.72/1.89  Inference rules
% 4.72/1.89  ----------------------
% 4.72/1.89  #Ref     : 0
% 4.72/1.89  #Sup     : 793
% 4.72/1.89  #Fact    : 0
% 4.72/1.89  #Define  : 0
% 4.72/1.89  #Split   : 63
% 4.72/1.89  #Chain   : 0
% 4.72/1.89  #Close   : 0
% 4.72/1.89  
% 4.72/1.89  Ordering : KBO
% 4.72/1.89  
% 4.72/1.89  Simplification rules
% 4.72/1.89  ----------------------
% 4.72/1.89  #Subsume      : 426
% 4.72/1.89  #Demod        : 334
% 4.72/1.89  #Tautology    : 134
% 4.72/1.89  #SimpNegUnit  : 48
% 4.72/1.89  #BackRed      : 163
% 4.72/1.89  
% 4.72/1.89  #Partial instantiations: 0
% 4.72/1.89  #Strategies tried      : 1
% 4.72/1.89  
% 4.72/1.89  Timing (in seconds)
% 4.72/1.89  ----------------------
% 4.72/1.89  Preprocessing        : 0.31
% 4.72/1.89  Parsing              : 0.16
% 4.72/1.90  CNF conversion       : 0.02
% 4.72/1.90  Main loop            : 0.80
% 4.72/1.90  Inferencing          : 0.27
% 4.72/1.90  Reduction            : 0.26
% 4.72/1.90  Demodulation         : 0.18
% 4.72/1.90  BG Simplification    : 0.03
% 4.72/1.90  Subsumption          : 0.16
% 4.72/1.90  Abstraction          : 0.04
% 4.72/1.90  MUC search           : 0.00
% 4.72/1.90  Cooper               : 0.00
% 4.72/1.90  Total                : 1.16
% 4.72/1.90  Index Insertion      : 0.00
% 4.72/1.90  Index Deletion       : 0.00
% 4.72/1.90  Index Matching       : 0.00
% 4.72/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
