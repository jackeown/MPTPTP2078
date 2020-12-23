%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:32 EST 2020

% Result     : Theorem 30.54s
% Output     : CNFRefutation 30.76s
% Verified   : 
% Statistics : Number of formulae       :  187 (2777 expanded)
%              Number of leaves         :   39 ( 876 expanded)
%              Depth                    :   17
%              Number of atoms          :  334 (8700 expanded)
%              Number of equality atoms :   77 (3375 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_156,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(k2_partfun1(A,B,D,C))
              & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
              & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_124,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k7_relat_1(B,A)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_118,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_136,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_66,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_91361,plain,(
    ! [C_2340,A_2341,B_2342] :
      ( v1_relat_1(C_2340)
      | ~ m1_subset_1(C_2340,k1_zfmisc_1(k2_zfmisc_1(A_2341,B_2342))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_91374,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_91361])).

tff(c_64,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_77,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_70,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_92018,plain,(
    ! [A_2419,B_2420,C_2421] :
      ( k1_relset_1(A_2419,B_2420,C_2421) = k1_relat_1(C_2421)
      | ~ m1_subset_1(C_2421,k1_zfmisc_1(k2_zfmisc_1(A_2419,B_2420))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_92037,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_92018])).

tff(c_93012,plain,(
    ! [B_2517,A_2518,C_2519] :
      ( k1_xboole_0 = B_2517
      | k1_relset_1(A_2518,B_2517,C_2519) = A_2518
      | ~ v1_funct_2(C_2519,A_2518,B_2517)
      | ~ m1_subset_1(C_2519,k1_zfmisc_1(k2_zfmisc_1(A_2518,B_2517))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_93025,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_93012])).

tff(c_93039,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_92037,c_93025])).

tff(c_93040,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_93039])).

tff(c_26,plain,(
    ! [B_19,A_18] :
      ( k1_relat_1(k7_relat_1(B_19,A_18)) = A_18
      | ~ r1_tarski(A_18,k1_relat_1(B_19))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_93052,plain,(
    ! [A_18] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_18)) = A_18
      | ~ r1_tarski(A_18,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93040,c_26])).

tff(c_93106,plain,(
    ! [A_2522] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_2522)) = A_2522
      | ~ r1_tarski(A_2522,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91374,c_93052])).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_92722,plain,(
    ! [A_2504,B_2505,C_2506,D_2507] :
      ( k2_partfun1(A_2504,B_2505,C_2506,D_2507) = k7_relat_1(C_2506,D_2507)
      | ~ m1_subset_1(C_2506,k1_zfmisc_1(k2_zfmisc_1(A_2504,B_2505)))
      | ~ v1_funct_1(C_2506) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_92731,plain,(
    ! [D_2507] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_2507) = k7_relat_1('#skF_4',D_2507)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_92722])).

tff(c_92743,plain,(
    ! [D_2507] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_2507) = k7_relat_1('#skF_4',D_2507) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_92731])).

tff(c_1353,plain,(
    ! [C_221,A_222,B_223] :
      ( v1_relat_1(C_221)
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(A_222,B_223))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1366,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_1353])).

tff(c_1497,plain,(
    ! [C_250,A_251,B_252] :
      ( v4_relat_1(C_250,A_251)
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(A_251,B_252))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1512,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_1497])).

tff(c_1568,plain,(
    ! [B_266,A_267] :
      ( k7_relat_1(B_266,A_267) = B_266
      | ~ v4_relat_1(B_266,A_267)
      | ~ v1_relat_1(B_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1577,plain,
    ( k7_relat_1('#skF_4','#skF_1') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1512,c_1568])).

tff(c_1582,plain,(
    k7_relat_1('#skF_4','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1366,c_1577])).

tff(c_28,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_21,A_20)),k2_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1586,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1582,c_28])).

tff(c_1598,plain,(
    r1_tarski(k2_relat_1('#skF_4'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1366,c_1586])).

tff(c_1748,plain,(
    ! [B_273,A_274] :
      ( v5_relat_1(B_273,A_274)
      | ~ r1_tarski(k2_relat_1(B_273),A_274)
      | ~ v1_relat_1(B_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1754,plain,
    ( v5_relat_1('#skF_4',k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1598,c_1748])).

tff(c_1765,plain,(
    v5_relat_1('#skF_4',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1366,c_1754])).

tff(c_1697,plain,(
    ! [B_271,A_272] :
      ( r1_tarski(k2_relat_1(B_271),A_272)
      | ~ v5_relat_1(B_271,A_272)
      | ~ v1_relat_1(B_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2890,plain,(
    ! [A_407,A_408,B_409] :
      ( r1_tarski(A_407,A_408)
      | ~ r1_tarski(A_407,k2_relat_1(B_409))
      | ~ v5_relat_1(B_409,A_408)
      | ~ v1_relat_1(B_409) ) ),
    inference(resolution,[status(thm)],[c_1697,c_2])).

tff(c_2910,plain,(
    ! [B_21,A_20,A_408] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_21,A_20)),A_408)
      | ~ v5_relat_1(B_21,A_408)
      | ~ v1_relat_1(B_21) ) ),
    inference(resolution,[status(thm)],[c_28,c_2890])).

tff(c_1438,plain,(
    ! [C_236,B_237,A_238] :
      ( v5_relat_1(C_236,B_237)
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1(A_238,B_237))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1453,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_1438])).

tff(c_2897,plain,(
    ! [A_408] :
      ( r1_tarski(k2_relat_1('#skF_4'),A_408)
      | ~ v5_relat_1('#skF_4',A_408)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1598,c_2890])).

tff(c_2912,plain,(
    ! [A_410] :
      ( r1_tarski(k2_relat_1('#skF_4'),A_410)
      | ~ v5_relat_1('#skF_4',A_410) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1366,c_2897])).

tff(c_1743,plain,(
    ! [A_1,A_272,B_271] :
      ( r1_tarski(A_1,A_272)
      | ~ r1_tarski(A_1,k2_relat_1(B_271))
      | ~ v5_relat_1(B_271,A_272)
      | ~ v1_relat_1(B_271) ) ),
    inference(resolution,[status(thm)],[c_1697,c_2])).

tff(c_15269,plain,(
    ! [A_936,B_937] :
      ( r1_tarski(k2_relat_1('#skF_4'),A_936)
      | ~ v5_relat_1(B_937,A_936)
      | ~ v1_relat_1(B_937)
      | ~ v5_relat_1('#skF_4',k2_relat_1(B_937)) ) ),
    inference(resolution,[status(thm)],[c_2912,c_1743])).

tff(c_15323,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4')
    | ~ v5_relat_1('#skF_4',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1453,c_15269])).

tff(c_15377,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1765,c_1366,c_15323])).

tff(c_15445,plain,(
    ! [A_938] :
      ( r1_tarski(A_938,'#skF_2')
      | ~ r1_tarski(A_938,k2_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_15377,c_2])).

tff(c_15518,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_21,A_20)),'#skF_2')
      | ~ v5_relat_1(B_21,k2_relat_1('#skF_4'))
      | ~ v1_relat_1(B_21) ) ),
    inference(resolution,[status(thm)],[c_2910,c_15445])).

tff(c_24,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k7_relat_1(B_17,A_16),B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1319,plain,(
    ! [A_213,B_214] :
      ( r1_tarski(A_213,B_214)
      | ~ m1_subset_1(A_213,k1_zfmisc_1(B_214)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1327,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_68,c_1319])).

tff(c_1409,plain,(
    ! [A_231,C_232,B_233] :
      ( r1_tarski(A_231,C_232)
      | ~ r1_tarski(B_233,C_232)
      | ~ r1_tarski(A_231,B_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1426,plain,(
    ! [A_235] :
      ( r1_tarski(A_235,k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_235,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1327,c_1409])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1365,plain,(
    ! [A_7,A_222,B_223] :
      ( v1_relat_1(A_7)
      | ~ r1_tarski(A_7,k2_zfmisc_1(A_222,B_223)) ) ),
    inference(resolution,[status(thm)],[c_14,c_1353])).

tff(c_1454,plain,(
    ! [A_239] :
      ( v1_relat_1(A_239)
      | ~ r1_tarski(A_239,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1426,c_1365])).

tff(c_1458,plain,(
    ! [A_16] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_16))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_1454])).

tff(c_1461,plain,(
    ! [A_16] : v1_relat_1(k7_relat_1('#skF_4',A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1366,c_1458])).

tff(c_3041,plain,(
    ! [A_411,B_412,C_413,D_414] :
      ( k2_partfun1(A_411,B_412,C_413,D_414) = k7_relat_1(C_413,D_414)
      | ~ m1_subset_1(C_413,k1_zfmisc_1(k2_zfmisc_1(A_411,B_412)))
      | ~ v1_funct_1(C_413) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_3048,plain,(
    ! [D_414] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_414) = k7_relat_1('#skF_4',D_414)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_3041])).

tff(c_3057,plain,(
    ! [D_414] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_414) = k7_relat_1('#skF_4',D_414) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3048])).

tff(c_2665,plain,(
    ! [A_384,B_385,C_386,D_387] :
      ( v1_funct_1(k2_partfun1(A_384,B_385,C_386,D_387))
      | ~ m1_subset_1(C_386,k1_zfmisc_1(k2_zfmisc_1(A_384,B_385)))
      | ~ v1_funct_1(C_386) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2670,plain,(
    ! [D_387] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_387))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_2665])).

tff(c_2678,plain,(
    ! [D_387] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_387)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2670])).

tff(c_3058,plain,(
    ! [D_387] : v1_funct_1(k7_relat_1('#skF_4',D_387)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3057,c_2678])).

tff(c_2170,plain,(
    ! [A_318,B_319,C_320] :
      ( k1_relset_1(A_318,B_319,C_320) = k1_relat_1(C_320)
      | ~ m1_subset_1(C_320,k1_zfmisc_1(k2_zfmisc_1(A_318,B_319))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2185,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_2170])).

tff(c_3218,plain,(
    ! [B_425,A_426,C_427] :
      ( k1_xboole_0 = B_425
      | k1_relset_1(A_426,B_425,C_427) = A_426
      | ~ v1_funct_2(C_427,A_426,B_425)
      | ~ m1_subset_1(C_427,k1_zfmisc_1(k2_zfmisc_1(A_426,B_425))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_3228,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_3218])).

tff(c_3239,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2185,c_3228])).

tff(c_3240,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_3239])).

tff(c_3252,plain,(
    ! [A_18] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_18)) = A_18
      | ~ r1_tarski(A_18,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3240,c_26])).

tff(c_3260,plain,(
    ! [A_18] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_18)) = A_18
      | ~ r1_tarski(A_18,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1366,c_3252])).

tff(c_2858,plain,(
    ! [B_405,A_406] :
      ( m1_subset_1(B_405,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_405),A_406)))
      | ~ r1_tarski(k2_relat_1(B_405),A_406)
      | ~ v1_funct_1(B_405)
      | ~ v1_relat_1(B_405) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6350,plain,(
    ! [B_553,A_554] :
      ( r1_tarski(B_553,k2_zfmisc_1(k1_relat_1(B_553),A_554))
      | ~ r1_tarski(k2_relat_1(B_553),A_554)
      | ~ v1_funct_1(B_553)
      | ~ v1_relat_1(B_553) ) ),
    inference(resolution,[status(thm)],[c_2858,c_12])).

tff(c_6400,plain,(
    ! [A_18,A_554] :
      ( r1_tarski(k7_relat_1('#skF_4',A_18),k2_zfmisc_1(A_18,A_554))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_18)),A_554)
      | ~ v1_funct_1(k7_relat_1('#skF_4',A_18))
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_18))
      | ~ r1_tarski(A_18,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3260,c_6350])).

tff(c_91013,plain,(
    ! [A_2325,A_2326] :
      ( r1_tarski(k7_relat_1('#skF_4',A_2325),k2_zfmisc_1(A_2325,A_2326))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_2325)),A_2326)
      | ~ r1_tarski(A_2325,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1461,c_3058,c_6400])).

tff(c_91071,plain,(
    ! [A_20] :
      ( r1_tarski(k7_relat_1('#skF_4',A_20),k2_zfmisc_1(A_20,'#skF_2'))
      | ~ r1_tarski(A_20,'#skF_1')
      | ~ v5_relat_1('#skF_4',k2_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_15518,c_91013])).

tff(c_91216,plain,(
    ! [A_2327] :
      ( r1_tarski(k7_relat_1('#skF_4',A_2327),k2_zfmisc_1(A_2327,'#skF_2'))
      | ~ r1_tarski(A_2327,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1366,c_1765,c_91071])).

tff(c_1291,plain,(
    ! [A_205,B_206,C_207,D_208] :
      ( v1_funct_1(k2_partfun1(A_205,B_206,C_207,D_208))
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(A_205,B_206)))
      | ~ v1_funct_1(C_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1296,plain,(
    ! [D_208] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_208))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_1291])).

tff(c_1304,plain,(
    ! [D_208] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_208)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1296])).

tff(c_62,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_101,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_1307,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1304,c_101])).

tff(c_1308,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_1316,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1308])).

tff(c_1408,plain,(
    ~ r1_tarski(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_14,c_1316])).

tff(c_3059,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4','#skF_3'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3057,c_1408])).

tff(c_91241,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_91216,c_3059])).

tff(c_91311,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_91241])).

tff(c_91313,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1308])).

tff(c_92035,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_91313,c_92018])).

tff(c_92746,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92743,c_92743,c_92035])).

tff(c_91312,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1308])).

tff(c_92752,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92743,c_91312])).

tff(c_92751,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92743,c_91313])).

tff(c_92903,plain,(
    ! [B_2511,C_2512,A_2513] :
      ( k1_xboole_0 = B_2511
      | v1_funct_2(C_2512,A_2513,B_2511)
      | k1_relset_1(A_2513,B_2511,C_2512) != A_2513
      | ~ m1_subset_1(C_2512,k1_zfmisc_1(k2_zfmisc_1(A_2513,B_2511))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_92906,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_92751,c_92903])).

tff(c_92925,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_92752,c_77,c_92906])).

tff(c_92932,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92746,c_92925])).

tff(c_93112,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_93106,c_92932])).

tff(c_93132,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_93112])).

tff(c_93133,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_8,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_93145,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93133,c_93133,c_8])).

tff(c_93134,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_93139,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93133,c_93134])).

tff(c_93153,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93145,c_93139,c_68])).

tff(c_93192,plain,(
    ! [A_2528,B_2529] :
      ( r1_tarski(A_2528,B_2529)
      | ~ m1_subset_1(A_2528,k1_zfmisc_1(B_2529)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_93196,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_93153,c_93192])).

tff(c_4,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_93170,plain,(
    ! [A_4] :
      ( A_4 = '#skF_1'
      | ~ r1_tarski(A_4,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93133,c_93133,c_4])).

tff(c_93200,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_93196,c_93170])).

tff(c_93140,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93139,c_70])).

tff(c_93207,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93200,c_93200,c_93140])).

tff(c_93206,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93200,c_93153])).

tff(c_93208,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93200,c_93200,c_93145])).

tff(c_99805,plain,(
    ! [A_3098,B_3099,C_3100,D_3101] :
      ( m1_subset_1(k2_partfun1(A_3098,B_3099,C_3100,D_3101),k1_zfmisc_1(k2_zfmisc_1(A_3098,B_3099)))
      | ~ m1_subset_1(C_3100,k1_zfmisc_1(k2_zfmisc_1(A_3098,B_3099)))
      | ~ v1_funct_1(C_3100) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_99836,plain,(
    ! [A_5,C_3100,D_3101] :
      ( m1_subset_1(k2_partfun1(A_5,'#skF_4',C_3100,D_3101),k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(C_3100,k1_zfmisc_1(k2_zfmisc_1(A_5,'#skF_4')))
      | ~ v1_funct_1(C_3100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93208,c_99805])).

tff(c_100885,plain,(
    ! [A_3174,C_3175,D_3176] :
      ( m1_subset_1(k2_partfun1(A_3174,'#skF_4',C_3175,D_3176),k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(C_3175,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_3175) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93208,c_99836])).

tff(c_93209,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93200,c_93139])).

tff(c_10,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_93154,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_1',B_6) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93133,c_93133,c_10])).

tff(c_93205,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_4',B_6) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93200,c_93200,c_93154])).

tff(c_95180,plain,(
    ! [A_2728,B_2729,C_2730,D_2731] :
      ( v1_funct_1(k2_partfun1(A_2728,B_2729,C_2730,D_2731))
      | ~ m1_subset_1(C_2730,k1_zfmisc_1(k2_zfmisc_1(A_2728,B_2729)))
      | ~ v1_funct_1(C_2730) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_95189,plain,(
    ! [A_2732,C_2733,D_2734] :
      ( v1_funct_1(k2_partfun1(A_2732,'#skF_4',C_2733,D_2734))
      | ~ m1_subset_1(C_2733,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_2733) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93208,c_95180])).

tff(c_95191,plain,(
    ! [A_2732,D_2734] :
      ( v1_funct_1(k2_partfun1(A_2732,'#skF_4','#skF_4',D_2734))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_93206,c_95189])).

tff(c_95197,plain,(
    ! [A_2732,D_2734] : v1_funct_1(k2_partfun1(A_2732,'#skF_4','#skF_4',D_2734)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_95191])).

tff(c_93171,plain,(
    ! [A_2525] :
      ( A_2525 = '#skF_1'
      | ~ r1_tarski(A_2525,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93133,c_93133,c_4])).

tff(c_93175,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_66,c_93171])).

tff(c_93203,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93200,c_93175])).

tff(c_93219,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93203,c_93200,c_93203,c_93203,c_93200,c_93203,c_93203,c_93200,c_62])).

tff(c_93220,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_93219])).

tff(c_93262,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93209,c_93220])).

tff(c_95201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95197,c_93262])).

tff(c_95202,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_4'),'#skF_4','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_93219])).

tff(c_95393,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4')
    | ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93209,c_93205,c_93209,c_93209,c_95202])).

tff(c_95394,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_95393])).

tff(c_100906,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_100885,c_95394])).

tff(c_100928,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_93206,c_100906])).

tff(c_100930,plain,(
    m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_95393])).

tff(c_100954,plain,(
    r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_100930,c_12])).

tff(c_93204,plain,(
    ! [A_4] :
      ( A_4 = '#skF_4'
      | ~ r1_tarski(A_4,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93200,c_93200,c_93170])).

tff(c_100970,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_100954,c_93204])).

tff(c_100929,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_95393])).

tff(c_100975,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100970,c_100929])).

tff(c_100982,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93207,c_100975])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:31:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 30.54/19.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 30.76/19.80  
% 30.76/19.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 30.76/19.81  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 30.76/19.81  
% 30.76/19.81  %Foreground sorts:
% 30.76/19.81  
% 30.76/19.81  
% 30.76/19.81  %Background operators:
% 30.76/19.81  
% 30.76/19.81  
% 30.76/19.81  %Foreground operators:
% 30.76/19.81  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 30.76/19.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 30.76/19.81  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 30.76/19.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 30.76/19.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 30.76/19.81  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 30.76/19.81  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 30.76/19.81  tff('#skF_2', type, '#skF_2': $i).
% 30.76/19.81  tff('#skF_3', type, '#skF_3': $i).
% 30.76/19.81  tff('#skF_1', type, '#skF_1': $i).
% 30.76/19.81  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 30.76/19.81  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 30.76/19.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 30.76/19.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 30.76/19.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 30.76/19.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 30.76/19.81  tff('#skF_4', type, '#skF_4': $i).
% 30.76/19.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 30.76/19.81  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 30.76/19.81  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 30.76/19.81  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 30.76/19.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 30.76/19.81  
% 30.76/19.83  tff(f_156, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 30.76/19.83  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 30.76/19.83  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 30.76/19.83  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 30.76/19.83  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 30.76/19.83  tff(f_124, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 30.76/19.83  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 30.76/19.83  tff(f_64, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 30.76/19.83  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k7_relat_1(B, A)), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_relat_1)).
% 30.76/19.83  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 30.76/19.83  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 30.76/19.83  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 30.76/19.83  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 30.76/19.83  tff(f_118, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 30.76/19.83  tff(f_136, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 30.76/19.83  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 30.76/19.83  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 30.76/19.83  tff(c_66, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_156])).
% 30.76/19.83  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_156])).
% 30.76/19.83  tff(c_91361, plain, (![C_2340, A_2341, B_2342]: (v1_relat_1(C_2340) | ~m1_subset_1(C_2340, k1_zfmisc_1(k2_zfmisc_1(A_2341, B_2342))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 30.76/19.83  tff(c_91374, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_91361])).
% 30.76/19.83  tff(c_64, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_156])).
% 30.76/19.83  tff(c_77, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_64])).
% 30.76/19.83  tff(c_70, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 30.76/19.83  tff(c_92018, plain, (![A_2419, B_2420, C_2421]: (k1_relset_1(A_2419, B_2420, C_2421)=k1_relat_1(C_2421) | ~m1_subset_1(C_2421, k1_zfmisc_1(k2_zfmisc_1(A_2419, B_2420))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 30.76/19.83  tff(c_92037, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_92018])).
% 30.76/19.83  tff(c_93012, plain, (![B_2517, A_2518, C_2519]: (k1_xboole_0=B_2517 | k1_relset_1(A_2518, B_2517, C_2519)=A_2518 | ~v1_funct_2(C_2519, A_2518, B_2517) | ~m1_subset_1(C_2519, k1_zfmisc_1(k2_zfmisc_1(A_2518, B_2517))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 30.76/19.83  tff(c_93025, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_93012])).
% 30.76/19.83  tff(c_93039, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_92037, c_93025])).
% 30.76/19.83  tff(c_93040, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_77, c_93039])).
% 30.76/19.83  tff(c_26, plain, (![B_19, A_18]: (k1_relat_1(k7_relat_1(B_19, A_18))=A_18 | ~r1_tarski(A_18, k1_relat_1(B_19)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_74])).
% 30.76/19.83  tff(c_93052, plain, (![A_18]: (k1_relat_1(k7_relat_1('#skF_4', A_18))=A_18 | ~r1_tarski(A_18, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_93040, c_26])).
% 30.76/19.83  tff(c_93106, plain, (![A_2522]: (k1_relat_1(k7_relat_1('#skF_4', A_2522))=A_2522 | ~r1_tarski(A_2522, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_91374, c_93052])).
% 30.76/19.83  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 30.76/19.83  tff(c_92722, plain, (![A_2504, B_2505, C_2506, D_2507]: (k2_partfun1(A_2504, B_2505, C_2506, D_2507)=k7_relat_1(C_2506, D_2507) | ~m1_subset_1(C_2506, k1_zfmisc_1(k2_zfmisc_1(A_2504, B_2505))) | ~v1_funct_1(C_2506))), inference(cnfTransformation, [status(thm)], [f_124])).
% 30.76/19.83  tff(c_92731, plain, (![D_2507]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_2507)=k7_relat_1('#skF_4', D_2507) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_92722])).
% 30.76/19.83  tff(c_92743, plain, (![D_2507]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_2507)=k7_relat_1('#skF_4', D_2507))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_92731])).
% 30.76/19.83  tff(c_1353, plain, (![C_221, A_222, B_223]: (v1_relat_1(C_221) | ~m1_subset_1(C_221, k1_zfmisc_1(k2_zfmisc_1(A_222, B_223))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 30.76/19.83  tff(c_1366, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_1353])).
% 30.76/19.83  tff(c_1497, plain, (![C_250, A_251, B_252]: (v4_relat_1(C_250, A_251) | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(A_251, B_252))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 30.76/19.83  tff(c_1512, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_1497])).
% 30.76/19.83  tff(c_1568, plain, (![B_266, A_267]: (k7_relat_1(B_266, A_267)=B_266 | ~v4_relat_1(B_266, A_267) | ~v1_relat_1(B_266))), inference(cnfTransformation, [status(thm)], [f_64])).
% 30.76/19.83  tff(c_1577, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1512, c_1568])).
% 30.76/19.83  tff(c_1582, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1366, c_1577])).
% 30.76/19.83  tff(c_28, plain, (![B_21, A_20]: (r1_tarski(k2_relat_1(k7_relat_1(B_21, A_20)), k2_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_78])).
% 30.76/19.83  tff(c_1586, plain, (r1_tarski(k2_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1582, c_28])).
% 30.76/19.83  tff(c_1598, plain, (r1_tarski(k2_relat_1('#skF_4'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1366, c_1586])).
% 30.76/19.83  tff(c_1748, plain, (![B_273, A_274]: (v5_relat_1(B_273, A_274) | ~r1_tarski(k2_relat_1(B_273), A_274) | ~v1_relat_1(B_273))), inference(cnfTransformation, [status(thm)], [f_58])).
% 30.76/19.83  tff(c_1754, plain, (v5_relat_1('#skF_4', k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1598, c_1748])).
% 30.76/19.83  tff(c_1765, plain, (v5_relat_1('#skF_4', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1366, c_1754])).
% 30.76/19.83  tff(c_1697, plain, (![B_271, A_272]: (r1_tarski(k2_relat_1(B_271), A_272) | ~v5_relat_1(B_271, A_272) | ~v1_relat_1(B_271))), inference(cnfTransformation, [status(thm)], [f_58])).
% 30.76/19.83  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 30.76/19.83  tff(c_2890, plain, (![A_407, A_408, B_409]: (r1_tarski(A_407, A_408) | ~r1_tarski(A_407, k2_relat_1(B_409)) | ~v5_relat_1(B_409, A_408) | ~v1_relat_1(B_409))), inference(resolution, [status(thm)], [c_1697, c_2])).
% 30.76/19.83  tff(c_2910, plain, (![B_21, A_20, A_408]: (r1_tarski(k2_relat_1(k7_relat_1(B_21, A_20)), A_408) | ~v5_relat_1(B_21, A_408) | ~v1_relat_1(B_21))), inference(resolution, [status(thm)], [c_28, c_2890])).
% 30.76/19.83  tff(c_1438, plain, (![C_236, B_237, A_238]: (v5_relat_1(C_236, B_237) | ~m1_subset_1(C_236, k1_zfmisc_1(k2_zfmisc_1(A_238, B_237))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 30.76/19.83  tff(c_1453, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_1438])).
% 30.76/19.83  tff(c_2897, plain, (![A_408]: (r1_tarski(k2_relat_1('#skF_4'), A_408) | ~v5_relat_1('#skF_4', A_408) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1598, c_2890])).
% 30.76/19.83  tff(c_2912, plain, (![A_410]: (r1_tarski(k2_relat_1('#skF_4'), A_410) | ~v5_relat_1('#skF_4', A_410))), inference(demodulation, [status(thm), theory('equality')], [c_1366, c_2897])).
% 30.76/19.83  tff(c_1743, plain, (![A_1, A_272, B_271]: (r1_tarski(A_1, A_272) | ~r1_tarski(A_1, k2_relat_1(B_271)) | ~v5_relat_1(B_271, A_272) | ~v1_relat_1(B_271))), inference(resolution, [status(thm)], [c_1697, c_2])).
% 30.76/19.83  tff(c_15269, plain, (![A_936, B_937]: (r1_tarski(k2_relat_1('#skF_4'), A_936) | ~v5_relat_1(B_937, A_936) | ~v1_relat_1(B_937) | ~v5_relat_1('#skF_4', k2_relat_1(B_937)))), inference(resolution, [status(thm)], [c_2912, c_1743])).
% 30.76/19.83  tff(c_15323, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4') | ~v5_relat_1('#skF_4', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1453, c_15269])).
% 30.76/19.83  tff(c_15377, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1765, c_1366, c_15323])).
% 30.76/19.83  tff(c_15445, plain, (![A_938]: (r1_tarski(A_938, '#skF_2') | ~r1_tarski(A_938, k2_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_15377, c_2])).
% 30.76/19.83  tff(c_15518, plain, (![B_21, A_20]: (r1_tarski(k2_relat_1(k7_relat_1(B_21, A_20)), '#skF_2') | ~v5_relat_1(B_21, k2_relat_1('#skF_4')) | ~v1_relat_1(B_21))), inference(resolution, [status(thm)], [c_2910, c_15445])).
% 30.76/19.83  tff(c_24, plain, (![B_17, A_16]: (r1_tarski(k7_relat_1(B_17, A_16), B_17) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_68])).
% 30.76/19.83  tff(c_1319, plain, (![A_213, B_214]: (r1_tarski(A_213, B_214) | ~m1_subset_1(A_213, k1_zfmisc_1(B_214)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 30.76/19.83  tff(c_1327, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_68, c_1319])).
% 30.76/19.83  tff(c_1409, plain, (![A_231, C_232, B_233]: (r1_tarski(A_231, C_232) | ~r1_tarski(B_233, C_232) | ~r1_tarski(A_231, B_233))), inference(cnfTransformation, [status(thm)], [f_31])).
% 30.76/19.83  tff(c_1426, plain, (![A_235]: (r1_tarski(A_235, k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski(A_235, '#skF_4'))), inference(resolution, [status(thm)], [c_1327, c_1409])).
% 30.76/19.83  tff(c_14, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 30.76/19.83  tff(c_1365, plain, (![A_7, A_222, B_223]: (v1_relat_1(A_7) | ~r1_tarski(A_7, k2_zfmisc_1(A_222, B_223)))), inference(resolution, [status(thm)], [c_14, c_1353])).
% 30.76/19.83  tff(c_1454, plain, (![A_239]: (v1_relat_1(A_239) | ~r1_tarski(A_239, '#skF_4'))), inference(resolution, [status(thm)], [c_1426, c_1365])).
% 30.76/19.83  tff(c_1458, plain, (![A_16]: (v1_relat_1(k7_relat_1('#skF_4', A_16)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_1454])).
% 30.76/19.83  tff(c_1461, plain, (![A_16]: (v1_relat_1(k7_relat_1('#skF_4', A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_1366, c_1458])).
% 30.76/19.83  tff(c_3041, plain, (![A_411, B_412, C_413, D_414]: (k2_partfun1(A_411, B_412, C_413, D_414)=k7_relat_1(C_413, D_414) | ~m1_subset_1(C_413, k1_zfmisc_1(k2_zfmisc_1(A_411, B_412))) | ~v1_funct_1(C_413))), inference(cnfTransformation, [status(thm)], [f_124])).
% 30.76/19.83  tff(c_3048, plain, (![D_414]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_414)=k7_relat_1('#skF_4', D_414) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_3041])).
% 30.76/19.83  tff(c_3057, plain, (![D_414]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_414)=k7_relat_1('#skF_4', D_414))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_3048])).
% 30.76/19.83  tff(c_2665, plain, (![A_384, B_385, C_386, D_387]: (v1_funct_1(k2_partfun1(A_384, B_385, C_386, D_387)) | ~m1_subset_1(C_386, k1_zfmisc_1(k2_zfmisc_1(A_384, B_385))) | ~v1_funct_1(C_386))), inference(cnfTransformation, [status(thm)], [f_118])).
% 30.76/19.83  tff(c_2670, plain, (![D_387]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_387)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_2665])).
% 30.76/19.83  tff(c_2678, plain, (![D_387]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_387)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2670])).
% 30.76/19.83  tff(c_3058, plain, (![D_387]: (v1_funct_1(k7_relat_1('#skF_4', D_387)))), inference(demodulation, [status(thm), theory('equality')], [c_3057, c_2678])).
% 30.76/19.83  tff(c_2170, plain, (![A_318, B_319, C_320]: (k1_relset_1(A_318, B_319, C_320)=k1_relat_1(C_320) | ~m1_subset_1(C_320, k1_zfmisc_1(k2_zfmisc_1(A_318, B_319))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 30.76/19.83  tff(c_2185, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_2170])).
% 30.76/19.83  tff(c_3218, plain, (![B_425, A_426, C_427]: (k1_xboole_0=B_425 | k1_relset_1(A_426, B_425, C_427)=A_426 | ~v1_funct_2(C_427, A_426, B_425) | ~m1_subset_1(C_427, k1_zfmisc_1(k2_zfmisc_1(A_426, B_425))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 30.76/19.83  tff(c_3228, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_3218])).
% 30.76/19.83  tff(c_3239, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2185, c_3228])).
% 30.76/19.83  tff(c_3240, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_77, c_3239])).
% 30.76/19.83  tff(c_3252, plain, (![A_18]: (k1_relat_1(k7_relat_1('#skF_4', A_18))=A_18 | ~r1_tarski(A_18, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3240, c_26])).
% 30.76/19.83  tff(c_3260, plain, (![A_18]: (k1_relat_1(k7_relat_1('#skF_4', A_18))=A_18 | ~r1_tarski(A_18, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1366, c_3252])).
% 30.76/19.83  tff(c_2858, plain, (![B_405, A_406]: (m1_subset_1(B_405, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_405), A_406))) | ~r1_tarski(k2_relat_1(B_405), A_406) | ~v1_funct_1(B_405) | ~v1_relat_1(B_405))), inference(cnfTransformation, [status(thm)], [f_136])).
% 30.76/19.83  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 30.76/19.83  tff(c_6350, plain, (![B_553, A_554]: (r1_tarski(B_553, k2_zfmisc_1(k1_relat_1(B_553), A_554)) | ~r1_tarski(k2_relat_1(B_553), A_554) | ~v1_funct_1(B_553) | ~v1_relat_1(B_553))), inference(resolution, [status(thm)], [c_2858, c_12])).
% 30.76/19.83  tff(c_6400, plain, (![A_18, A_554]: (r1_tarski(k7_relat_1('#skF_4', A_18), k2_zfmisc_1(A_18, A_554)) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_18)), A_554) | ~v1_funct_1(k7_relat_1('#skF_4', A_18)) | ~v1_relat_1(k7_relat_1('#skF_4', A_18)) | ~r1_tarski(A_18, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_3260, c_6350])).
% 30.76/19.83  tff(c_91013, plain, (![A_2325, A_2326]: (r1_tarski(k7_relat_1('#skF_4', A_2325), k2_zfmisc_1(A_2325, A_2326)) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_2325)), A_2326) | ~r1_tarski(A_2325, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1461, c_3058, c_6400])).
% 30.76/19.83  tff(c_91071, plain, (![A_20]: (r1_tarski(k7_relat_1('#skF_4', A_20), k2_zfmisc_1(A_20, '#skF_2')) | ~r1_tarski(A_20, '#skF_1') | ~v5_relat_1('#skF_4', k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_15518, c_91013])).
% 30.76/19.83  tff(c_91216, plain, (![A_2327]: (r1_tarski(k7_relat_1('#skF_4', A_2327), k2_zfmisc_1(A_2327, '#skF_2')) | ~r1_tarski(A_2327, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1366, c_1765, c_91071])).
% 30.76/19.83  tff(c_1291, plain, (![A_205, B_206, C_207, D_208]: (v1_funct_1(k2_partfun1(A_205, B_206, C_207, D_208)) | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(A_205, B_206))) | ~v1_funct_1(C_207))), inference(cnfTransformation, [status(thm)], [f_118])).
% 30.76/19.83  tff(c_1296, plain, (![D_208]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_208)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_1291])).
% 30.76/19.83  tff(c_1304, plain, (![D_208]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_208)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1296])).
% 30.76/19.83  tff(c_62, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_156])).
% 30.76/19.83  tff(c_101, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_62])).
% 30.76/19.83  tff(c_1307, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1304, c_101])).
% 30.76/19.83  tff(c_1308, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_62])).
% 30.76/19.83  tff(c_1316, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1308])).
% 30.76/19.83  tff(c_1408, plain, (~r1_tarski(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_14, c_1316])).
% 30.76/19.83  tff(c_3059, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_3'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3057, c_1408])).
% 30.76/19.83  tff(c_91241, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_91216, c_3059])).
% 30.76/19.83  tff(c_91311, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_91241])).
% 30.76/19.83  tff(c_91313, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_1308])).
% 30.76/19.83  tff(c_92035, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_91313, c_92018])).
% 30.76/19.83  tff(c_92746, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_92743, c_92743, c_92035])).
% 30.76/19.83  tff(c_91312, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_1308])).
% 30.76/19.83  tff(c_92752, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_92743, c_91312])).
% 30.76/19.83  tff(c_92751, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_92743, c_91313])).
% 30.76/19.83  tff(c_92903, plain, (![B_2511, C_2512, A_2513]: (k1_xboole_0=B_2511 | v1_funct_2(C_2512, A_2513, B_2511) | k1_relset_1(A_2513, B_2511, C_2512)!=A_2513 | ~m1_subset_1(C_2512, k1_zfmisc_1(k2_zfmisc_1(A_2513, B_2511))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 30.76/19.83  tff(c_92906, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_92751, c_92903])).
% 30.76/19.83  tff(c_92925, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_92752, c_77, c_92906])).
% 30.76/19.83  tff(c_92932, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_92746, c_92925])).
% 30.76/19.83  tff(c_93112, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_93106, c_92932])).
% 30.76/19.83  tff(c_93132, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_93112])).
% 30.76/19.83  tff(c_93133, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_64])).
% 30.76/19.83  tff(c_8, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 30.76/19.83  tff(c_93145, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_93133, c_93133, c_8])).
% 30.76/19.83  tff(c_93134, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_64])).
% 30.76/19.83  tff(c_93139, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_93133, c_93134])).
% 30.76/19.83  tff(c_93153, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_93145, c_93139, c_68])).
% 30.76/19.83  tff(c_93192, plain, (![A_2528, B_2529]: (r1_tarski(A_2528, B_2529) | ~m1_subset_1(A_2528, k1_zfmisc_1(B_2529)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 30.76/19.83  tff(c_93196, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_93153, c_93192])).
% 30.76/19.83  tff(c_4, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 30.76/19.83  tff(c_93170, plain, (![A_4]: (A_4='#skF_1' | ~r1_tarski(A_4, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_93133, c_93133, c_4])).
% 30.76/19.83  tff(c_93200, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_93196, c_93170])).
% 30.76/19.83  tff(c_93140, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_93139, c_70])).
% 30.76/19.83  tff(c_93207, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_93200, c_93200, c_93140])).
% 30.76/19.83  tff(c_93206, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_93200, c_93153])).
% 30.76/19.83  tff(c_93208, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_93200, c_93200, c_93145])).
% 30.76/19.83  tff(c_99805, plain, (![A_3098, B_3099, C_3100, D_3101]: (m1_subset_1(k2_partfun1(A_3098, B_3099, C_3100, D_3101), k1_zfmisc_1(k2_zfmisc_1(A_3098, B_3099))) | ~m1_subset_1(C_3100, k1_zfmisc_1(k2_zfmisc_1(A_3098, B_3099))) | ~v1_funct_1(C_3100))), inference(cnfTransformation, [status(thm)], [f_118])).
% 30.76/19.83  tff(c_99836, plain, (![A_5, C_3100, D_3101]: (m1_subset_1(k2_partfun1(A_5, '#skF_4', C_3100, D_3101), k1_zfmisc_1('#skF_4')) | ~m1_subset_1(C_3100, k1_zfmisc_1(k2_zfmisc_1(A_5, '#skF_4'))) | ~v1_funct_1(C_3100))), inference(superposition, [status(thm), theory('equality')], [c_93208, c_99805])).
% 30.76/19.83  tff(c_100885, plain, (![A_3174, C_3175, D_3176]: (m1_subset_1(k2_partfun1(A_3174, '#skF_4', C_3175, D_3176), k1_zfmisc_1('#skF_4')) | ~m1_subset_1(C_3175, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_3175))), inference(demodulation, [status(thm), theory('equality')], [c_93208, c_99836])).
% 30.76/19.83  tff(c_93209, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_93200, c_93139])).
% 30.76/19.83  tff(c_10, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 30.76/19.83  tff(c_93154, plain, (![B_6]: (k2_zfmisc_1('#skF_1', B_6)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_93133, c_93133, c_10])).
% 30.76/19.83  tff(c_93205, plain, (![B_6]: (k2_zfmisc_1('#skF_4', B_6)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_93200, c_93200, c_93154])).
% 30.76/19.83  tff(c_95180, plain, (![A_2728, B_2729, C_2730, D_2731]: (v1_funct_1(k2_partfun1(A_2728, B_2729, C_2730, D_2731)) | ~m1_subset_1(C_2730, k1_zfmisc_1(k2_zfmisc_1(A_2728, B_2729))) | ~v1_funct_1(C_2730))), inference(cnfTransformation, [status(thm)], [f_118])).
% 30.76/19.83  tff(c_95189, plain, (![A_2732, C_2733, D_2734]: (v1_funct_1(k2_partfun1(A_2732, '#skF_4', C_2733, D_2734)) | ~m1_subset_1(C_2733, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_2733))), inference(superposition, [status(thm), theory('equality')], [c_93208, c_95180])).
% 30.76/19.83  tff(c_95191, plain, (![A_2732, D_2734]: (v1_funct_1(k2_partfun1(A_2732, '#skF_4', '#skF_4', D_2734)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_93206, c_95189])).
% 30.76/19.83  tff(c_95197, plain, (![A_2732, D_2734]: (v1_funct_1(k2_partfun1(A_2732, '#skF_4', '#skF_4', D_2734)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_95191])).
% 30.76/19.83  tff(c_93171, plain, (![A_2525]: (A_2525='#skF_1' | ~r1_tarski(A_2525, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_93133, c_93133, c_4])).
% 30.76/19.83  tff(c_93175, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_66, c_93171])).
% 30.76/19.83  tff(c_93203, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_93200, c_93175])).
% 30.76/19.83  tff(c_93219, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_93203, c_93200, c_93203, c_93203, c_93200, c_93203, c_93203, c_93200, c_62])).
% 30.76/19.83  tff(c_93220, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_4'))), inference(splitLeft, [status(thm)], [c_93219])).
% 30.76/19.83  tff(c_93262, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_93209, c_93220])).
% 30.76/19.83  tff(c_95201, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95197, c_93262])).
% 30.76/19.83  tff(c_95202, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_4'), '#skF_4', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(splitRight, [status(thm)], [c_93219])).
% 30.76/19.83  tff(c_95393, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4') | ~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_93209, c_93205, c_93209, c_93209, c_95202])).
% 30.76/19.83  tff(c_95394, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_95393])).
% 30.76/19.83  tff(c_100906, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_100885, c_95394])).
% 30.76/19.83  tff(c_100928, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_93206, c_100906])).
% 30.76/19.83  tff(c_100930, plain, (m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_95393])).
% 30.76/19.83  tff(c_100954, plain, (r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_100930, c_12])).
% 30.76/19.83  tff(c_93204, plain, (![A_4]: (A_4='#skF_4' | ~r1_tarski(A_4, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_93200, c_93200, c_93170])).
% 30.76/19.83  tff(c_100970, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_100954, c_93204])).
% 30.76/19.83  tff(c_100929, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_95393])).
% 30.76/19.83  tff(c_100975, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_100970, c_100929])).
% 30.76/19.83  tff(c_100982, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93207, c_100975])).
% 30.76/19.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 30.76/19.83  
% 30.76/19.83  Inference rules
% 30.76/19.83  ----------------------
% 30.76/19.83  #Ref     : 0
% 30.76/19.83  #Sup     : 21800
% 30.76/19.83  #Fact    : 0
% 30.76/19.83  #Define  : 0
% 30.76/19.83  #Split   : 65
% 30.76/19.83  #Chain   : 0
% 30.76/19.83  #Close   : 0
% 30.76/19.83  
% 30.76/19.83  Ordering : KBO
% 30.76/19.83  
% 30.76/19.83  Simplification rules
% 30.76/19.83  ----------------------
% 30.76/19.83  #Subsume      : 9778
% 30.76/19.83  #Demod        : 26125
% 30.76/19.83  #Tautology    : 4911
% 30.76/19.83  #SimpNegUnit  : 440
% 30.76/19.83  #BackRed      : 155
% 30.76/19.83  
% 30.76/19.83  #Partial instantiations: 0
% 30.76/19.83  #Strategies tried      : 1
% 30.76/19.83  
% 30.76/19.83  Timing (in seconds)
% 30.76/19.83  ----------------------
% 30.76/19.84  Preprocessing        : 0.35
% 30.76/19.84  Parsing              : 0.19
% 30.76/19.84  CNF conversion       : 0.02
% 30.76/19.84  Main loop            : 18.69
% 30.76/19.84  Inferencing          : 3.03
% 30.76/19.84  Reduction            : 7.88
% 30.76/19.84  Demodulation         : 6.23
% 30.76/19.84  BG Simplification    : 0.21
% 30.76/19.84  Subsumption          : 6.69
% 30.76/19.84  Abstraction          : 0.43
% 30.76/19.84  MUC search           : 0.00
% 30.76/19.84  Cooper               : 0.00
% 30.76/19.84  Total                : 19.10
% 30.76/19.84  Index Insertion      : 0.00
% 30.76/19.84  Index Deletion       : 0.00
% 30.76/19.84  Index Matching       : 0.00
% 30.76/19.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
