%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:03 EST 2020

% Result     : Theorem 4.68s
% Output     : CNFRefutation 4.68s
% Verified   : 
% Statistics : Number of formulae       :  103 (1033 expanded)
%              Number of leaves         :   35 ( 338 expanded)
%              Depth                    :   14
%              Number of atoms          :  175 (3194 expanded)
%              Number of equality atoms :   28 (1246 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > #nlpp > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_partfun1(C,D)
             => ( ( B = k1_xboole_0
                  & A != k1_xboole_0 )
                | r2_hidden(D,k5_partfun1(A,B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_2)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_42,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( D = k5_partfun1(A,B,C)
        <=> ! [E] :
              ( r2_hidden(E,D)
            <=> ? [F] :
                  ( v1_funct_1(F)
                  & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(A,B)))
                  & F = E
                  & v1_partfun1(F,A)
                  & r1_partfun1(C,F) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_partfun1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_98,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(c_86,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_72,plain,(
    ~ r2_hidden('#skF_9',k5_partfun1('#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_76,plain,(
    r1_partfun1('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_84,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_82,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_74,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_96,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_80,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_78,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_247,plain,(
    ! [C_89,A_90,B_91] :
      ( v1_partfun1(C_89,A_90)
      | ~ v1_funct_2(C_89,A_90,B_91)
      | ~ v1_funct_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91)))
      | v1_xboole_0(B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_263,plain,
    ( v1_partfun1('#skF_9','#skF_6')
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7')
    | ~ v1_funct_1('#skF_9')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_78,c_247])).

tff(c_275,plain,
    ( v1_partfun1('#skF_9','#skF_6')
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_263])).

tff(c_277,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_275])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_230,plain,(
    ! [C_86,B_87,A_88] :
      ( ~ v1_xboole_0(C_86)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(C_86))
      | ~ r2_hidden(A_88,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_289,plain,(
    ! [B_94,A_95,A_96] :
      ( ~ v1_xboole_0(B_94)
      | ~ r2_hidden(A_95,A_96)
      | ~ r1_tarski(A_96,B_94) ) ),
    inference(resolution,[status(thm)],[c_24,c_230])).

tff(c_293,plain,(
    ! [B_97,A_98,B_99] :
      ( ~ v1_xboole_0(B_97)
      | ~ r1_tarski(A_98,B_97)
      | r1_tarski(A_98,B_99) ) ),
    inference(resolution,[status(thm)],[c_6,c_289])).

tff(c_328,plain,(
    ! [B_104,B_105] :
      ( ~ v1_xboole_0(B_104)
      | r1_tarski(B_104,B_105) ) ),
    inference(resolution,[status(thm)],[c_12,c_293])).

tff(c_14,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_340,plain,(
    ! [B_106] :
      ( k1_xboole_0 = B_106
      | ~ v1_xboole_0(B_106) ) ),
    inference(resolution,[status(thm)],[c_328,c_14])).

tff(c_343,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_277,c_340])).

tff(c_347,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_343])).

tff(c_348,plain,(
    v1_partfun1('#skF_9','#skF_6') ),
    inference(splitRight,[status(thm)],[c_275])).

tff(c_1386,plain,(
    ! [F_270,A_271,B_272,C_273] :
      ( r2_hidden(F_270,k5_partfun1(A_271,B_272,C_273))
      | ~ r1_partfun1(C_273,F_270)
      | ~ v1_partfun1(F_270,A_271)
      | ~ m1_subset_1(F_270,k1_zfmisc_1(k2_zfmisc_1(A_271,B_272)))
      | ~ v1_funct_1(F_270)
      | ~ m1_subset_1(C_273,k1_zfmisc_1(k2_zfmisc_1(A_271,B_272)))
      | ~ v1_funct_1(C_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1399,plain,(
    ! [C_273] :
      ( r2_hidden('#skF_9',k5_partfun1('#skF_6','#skF_7',C_273))
      | ~ r1_partfun1(C_273,'#skF_9')
      | ~ v1_partfun1('#skF_9','#skF_6')
      | ~ v1_funct_1('#skF_9')
      | ~ m1_subset_1(C_273,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ v1_funct_1(C_273) ) ),
    inference(resolution,[status(thm)],[c_78,c_1386])).

tff(c_1415,plain,(
    ! [C_274] :
      ( r2_hidden('#skF_9',k5_partfun1('#skF_6','#skF_7',C_274))
      | ~ r1_partfun1(C_274,'#skF_9')
      | ~ m1_subset_1(C_274,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ v1_funct_1(C_274) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_348,c_1399])).

tff(c_1426,plain,
    ( r2_hidden('#skF_9',k5_partfun1('#skF_6','#skF_7','#skF_8'))
    | ~ r1_partfun1('#skF_8','#skF_9')
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_84,c_1415])).

tff(c_1434,plain,(
    r2_hidden('#skF_9',k5_partfun1('#skF_6','#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_76,c_1426])).

tff(c_1436,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1434])).

tff(c_1437,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_18,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1439,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1437,c_1437,c_18])).

tff(c_1438,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_1444,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1437,c_1438])).

tff(c_1484,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1439,c_1444,c_84])).

tff(c_1487,plain,(
    ! [A_281,B_282] :
      ( r1_tarski(A_281,B_282)
      | ~ m1_subset_1(A_281,k1_zfmisc_1(B_282)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1498,plain,(
    r1_tarski('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_1484,c_1487])).

tff(c_1476,plain,(
    ! [A_8] :
      ( A_8 = '#skF_6'
      | ~ r1_tarski(A_8,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1437,c_1437,c_14])).

tff(c_1503,plain,(
    '#skF_6' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1498,c_1476])).

tff(c_1506,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1503,c_1484])).

tff(c_1450,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1444,c_78])).

tff(c_1452,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1439,c_1450])).

tff(c_1499,plain,(
    r1_tarski('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_1452,c_1487])).

tff(c_1527,plain,(
    r1_tarski('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1503,c_1499])).

tff(c_1573,plain,(
    ! [A_286] :
      ( A_286 = '#skF_8'
      | ~ r1_tarski(A_286,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1503,c_1503,c_1476])).

tff(c_1581,plain,(
    '#skF_9' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1527,c_1573])).

tff(c_1587,plain,(
    r1_partfun1('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1581,c_76])).

tff(c_1510,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1503,c_1503,c_1439])).

tff(c_1533,plain,(
    ! [A_284] : k2_zfmisc_1(A_284,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1503,c_1503,c_1439])).

tff(c_70,plain,(
    ! [A_62] : m1_subset_1(k6_partfun1(A_62),k1_zfmisc_1(k2_zfmisc_1(A_62,A_62))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1539,plain,(
    m1_subset_1(k6_partfun1('#skF_8'),k1_zfmisc_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1533,c_70])).

tff(c_22,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1600,plain,(
    r1_tarski(k6_partfun1('#skF_8'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_1539,c_22])).

tff(c_1507,plain,(
    ! [A_8] :
      ( A_8 = '#skF_8'
      | ~ r1_tarski(A_8,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1503,c_1503,c_1476])).

tff(c_1604,plain,(
    k6_partfun1('#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1600,c_1507])).

tff(c_68,plain,(
    ! [A_62] : v1_partfun1(k6_partfun1(A_62),A_62) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2287,plain,(
    ! [F_453,A_454,B_455,C_456] :
      ( r2_hidden(F_453,k5_partfun1(A_454,B_455,C_456))
      | ~ r1_partfun1(C_456,F_453)
      | ~ v1_partfun1(F_453,A_454)
      | ~ m1_subset_1(F_453,k1_zfmisc_1(k2_zfmisc_1(A_454,B_455)))
      | ~ v1_funct_1(F_453)
      | ~ m1_subset_1(C_456,k1_zfmisc_1(k2_zfmisc_1(A_454,B_455)))
      | ~ v1_funct_1(C_456) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2295,plain,(
    ! [A_62,C_456] :
      ( r2_hidden(k6_partfun1(A_62),k5_partfun1(A_62,A_62,C_456))
      | ~ r1_partfun1(C_456,k6_partfun1(A_62))
      | ~ v1_partfun1(k6_partfun1(A_62),A_62)
      | ~ v1_funct_1(k6_partfun1(A_62))
      | ~ m1_subset_1(C_456,k1_zfmisc_1(k2_zfmisc_1(A_62,A_62)))
      | ~ v1_funct_1(C_456) ) ),
    inference(resolution,[status(thm)],[c_70,c_2287])).

tff(c_2373,plain,(
    ! [A_473,C_474] :
      ( r2_hidden(k6_partfun1(A_473),k5_partfun1(A_473,A_473,C_474))
      | ~ r1_partfun1(C_474,k6_partfun1(A_473))
      | ~ v1_funct_1(k6_partfun1(A_473))
      | ~ m1_subset_1(C_474,k1_zfmisc_1(k2_zfmisc_1(A_473,A_473)))
      | ~ v1_funct_1(C_474) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2295])).

tff(c_2382,plain,(
    ! [C_474] :
      ( r2_hidden('#skF_8',k5_partfun1('#skF_8','#skF_8',C_474))
      | ~ r1_partfun1(C_474,k6_partfun1('#skF_8'))
      | ~ v1_funct_1(k6_partfun1('#skF_8'))
      | ~ m1_subset_1(C_474,k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_8')))
      | ~ v1_funct_1(C_474) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1604,c_2373])).

tff(c_2388,plain,(
    ! [C_475] :
      ( r2_hidden('#skF_8',k5_partfun1('#skF_8','#skF_8',C_475))
      | ~ r1_partfun1(C_475,'#skF_8')
      | ~ m1_subset_1(C_475,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_1(C_475) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1510,c_86,c_1604,c_1604,c_2382])).

tff(c_1485,plain,(
    ~ r2_hidden('#skF_9',k5_partfun1('#skF_6','#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1444,c_72])).

tff(c_1505,plain,(
    ~ r2_hidden('#skF_9',k5_partfun1('#skF_8','#skF_8','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1503,c_1503,c_1485])).

tff(c_1620,plain,(
    ~ r2_hidden('#skF_8',k5_partfun1('#skF_8','#skF_8','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1581,c_1505])).

tff(c_2397,plain,
    ( ~ r1_partfun1('#skF_8','#skF_8')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8'))
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_2388,c_1620])).

tff(c_2405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1506,c_1587,c_2397])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:18:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.68/1.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.68/1.85  
% 4.68/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.68/1.85  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > #nlpp > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_1
% 4.68/1.85  
% 4.68/1.85  %Foreground sorts:
% 4.68/1.85  
% 4.68/1.85  
% 4.68/1.85  %Background operators:
% 4.68/1.85  
% 4.68/1.85  
% 4.68/1.85  %Foreground operators:
% 4.68/1.85  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.68/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.68/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.68/1.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.68/1.85  tff('#skF_7', type, '#skF_7': $i).
% 4.68/1.85  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i) > $i).
% 4.68/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.68/1.85  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.68/1.85  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.68/1.85  tff('#skF_6', type, '#skF_6': $i).
% 4.68/1.85  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.68/1.85  tff('#skF_9', type, '#skF_9': $i).
% 4.68/1.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.68/1.85  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 4.68/1.85  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.68/1.85  tff('#skF_8', type, '#skF_8': $i).
% 4.68/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.68/1.85  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.68/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.68/1.85  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.68/1.85  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 4.68/1.85  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.68/1.85  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.68/1.85  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 4.68/1.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.68/1.85  
% 4.68/1.87  tff(f_119, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_hidden(D, k5_partfun1(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_2)).
% 4.68/1.87  tff(f_73, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 4.68/1.87  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.68/1.87  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.68/1.87  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.68/1.87  tff(f_59, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 4.68/1.87  tff(f_42, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 4.68/1.87  tff(f_94, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((D = k5_partfun1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> (?[F]: ((((v1_funct_1(F) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & (F = E)) & v1_partfun1(F, A)) & r1_partfun1(C, F))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_partfun1)).
% 4.68/1.87  tff(f_48, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.68/1.87  tff(f_98, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 4.68/1.87  tff(c_86, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.68/1.87  tff(c_72, plain, (~r2_hidden('#skF_9', k5_partfun1('#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.68/1.87  tff(c_76, plain, (r1_partfun1('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.68/1.87  tff(c_84, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.68/1.87  tff(c_82, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.68/1.87  tff(c_74, plain, (k1_xboole_0='#skF_6' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.68/1.87  tff(c_96, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_74])).
% 4.68/1.87  tff(c_80, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.68/1.87  tff(c_78, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.68/1.87  tff(c_247, plain, (![C_89, A_90, B_91]: (v1_partfun1(C_89, A_90) | ~v1_funct_2(C_89, A_90, B_91) | ~v1_funct_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))) | v1_xboole_0(B_91))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.68/1.87  tff(c_263, plain, (v1_partfun1('#skF_9', '#skF_6') | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7') | ~v1_funct_1('#skF_9') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_78, c_247])).
% 4.68/1.87  tff(c_275, plain, (v1_partfun1('#skF_9', '#skF_6') | v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_263])).
% 4.68/1.87  tff(c_277, plain, (v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_275])).
% 4.68/1.87  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.68/1.87  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.68/1.87  tff(c_24, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.68/1.87  tff(c_230, plain, (![C_86, B_87, A_88]: (~v1_xboole_0(C_86) | ~m1_subset_1(B_87, k1_zfmisc_1(C_86)) | ~r2_hidden(A_88, B_87))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.68/1.87  tff(c_289, plain, (![B_94, A_95, A_96]: (~v1_xboole_0(B_94) | ~r2_hidden(A_95, A_96) | ~r1_tarski(A_96, B_94))), inference(resolution, [status(thm)], [c_24, c_230])).
% 4.68/1.87  tff(c_293, plain, (![B_97, A_98, B_99]: (~v1_xboole_0(B_97) | ~r1_tarski(A_98, B_97) | r1_tarski(A_98, B_99))), inference(resolution, [status(thm)], [c_6, c_289])).
% 4.68/1.87  tff(c_328, plain, (![B_104, B_105]: (~v1_xboole_0(B_104) | r1_tarski(B_104, B_105))), inference(resolution, [status(thm)], [c_12, c_293])).
% 4.68/1.87  tff(c_14, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.68/1.87  tff(c_340, plain, (![B_106]: (k1_xboole_0=B_106 | ~v1_xboole_0(B_106))), inference(resolution, [status(thm)], [c_328, c_14])).
% 4.68/1.87  tff(c_343, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_277, c_340])).
% 4.68/1.87  tff(c_347, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_343])).
% 4.68/1.87  tff(c_348, plain, (v1_partfun1('#skF_9', '#skF_6')), inference(splitRight, [status(thm)], [c_275])).
% 4.68/1.87  tff(c_1386, plain, (![F_270, A_271, B_272, C_273]: (r2_hidden(F_270, k5_partfun1(A_271, B_272, C_273)) | ~r1_partfun1(C_273, F_270) | ~v1_partfun1(F_270, A_271) | ~m1_subset_1(F_270, k1_zfmisc_1(k2_zfmisc_1(A_271, B_272))) | ~v1_funct_1(F_270) | ~m1_subset_1(C_273, k1_zfmisc_1(k2_zfmisc_1(A_271, B_272))) | ~v1_funct_1(C_273))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.68/1.87  tff(c_1399, plain, (![C_273]: (r2_hidden('#skF_9', k5_partfun1('#skF_6', '#skF_7', C_273)) | ~r1_partfun1(C_273, '#skF_9') | ~v1_partfun1('#skF_9', '#skF_6') | ~v1_funct_1('#skF_9') | ~m1_subset_1(C_273, k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~v1_funct_1(C_273))), inference(resolution, [status(thm)], [c_78, c_1386])).
% 4.68/1.87  tff(c_1415, plain, (![C_274]: (r2_hidden('#skF_9', k5_partfun1('#skF_6', '#skF_7', C_274)) | ~r1_partfun1(C_274, '#skF_9') | ~m1_subset_1(C_274, k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~v1_funct_1(C_274))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_348, c_1399])).
% 4.68/1.87  tff(c_1426, plain, (r2_hidden('#skF_9', k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | ~r1_partfun1('#skF_8', '#skF_9') | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_84, c_1415])).
% 4.68/1.87  tff(c_1434, plain, (r2_hidden('#skF_9', k5_partfun1('#skF_6', '#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_76, c_1426])).
% 4.68/1.87  tff(c_1436, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_1434])).
% 4.68/1.87  tff(c_1437, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_74])).
% 4.68/1.87  tff(c_18, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.68/1.87  tff(c_1439, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1437, c_1437, c_18])).
% 4.68/1.87  tff(c_1438, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_74])).
% 4.68/1.87  tff(c_1444, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1437, c_1438])).
% 4.68/1.87  tff(c_1484, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1439, c_1444, c_84])).
% 4.68/1.87  tff(c_1487, plain, (![A_281, B_282]: (r1_tarski(A_281, B_282) | ~m1_subset_1(A_281, k1_zfmisc_1(B_282)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.68/1.87  tff(c_1498, plain, (r1_tarski('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_1484, c_1487])).
% 4.68/1.87  tff(c_1476, plain, (![A_8]: (A_8='#skF_6' | ~r1_tarski(A_8, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1437, c_1437, c_14])).
% 4.68/1.87  tff(c_1503, plain, ('#skF_6'='#skF_8'), inference(resolution, [status(thm)], [c_1498, c_1476])).
% 4.68/1.87  tff(c_1506, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1503, c_1484])).
% 4.68/1.87  tff(c_1450, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_1444, c_78])).
% 4.68/1.87  tff(c_1452, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1439, c_1450])).
% 4.68/1.87  tff(c_1499, plain, (r1_tarski('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_1452, c_1487])).
% 4.68/1.87  tff(c_1527, plain, (r1_tarski('#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1503, c_1499])).
% 4.68/1.87  tff(c_1573, plain, (![A_286]: (A_286='#skF_8' | ~r1_tarski(A_286, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1503, c_1503, c_1476])).
% 4.68/1.87  tff(c_1581, plain, ('#skF_9'='#skF_8'), inference(resolution, [status(thm)], [c_1527, c_1573])).
% 4.68/1.87  tff(c_1587, plain, (r1_partfun1('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1581, c_76])).
% 4.68/1.87  tff(c_1510, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1503, c_1503, c_1439])).
% 4.68/1.87  tff(c_1533, plain, (![A_284]: (k2_zfmisc_1(A_284, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1503, c_1503, c_1439])).
% 4.68/1.87  tff(c_70, plain, (![A_62]: (m1_subset_1(k6_partfun1(A_62), k1_zfmisc_1(k2_zfmisc_1(A_62, A_62))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.68/1.87  tff(c_1539, plain, (m1_subset_1(k6_partfun1('#skF_8'), k1_zfmisc_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1533, c_70])).
% 4.68/1.87  tff(c_22, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.68/1.87  tff(c_1600, plain, (r1_tarski(k6_partfun1('#skF_8'), '#skF_8')), inference(resolution, [status(thm)], [c_1539, c_22])).
% 4.68/1.87  tff(c_1507, plain, (![A_8]: (A_8='#skF_8' | ~r1_tarski(A_8, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1503, c_1503, c_1476])).
% 4.68/1.87  tff(c_1604, plain, (k6_partfun1('#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_1600, c_1507])).
% 4.68/1.87  tff(c_68, plain, (![A_62]: (v1_partfun1(k6_partfun1(A_62), A_62))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.68/1.87  tff(c_2287, plain, (![F_453, A_454, B_455, C_456]: (r2_hidden(F_453, k5_partfun1(A_454, B_455, C_456)) | ~r1_partfun1(C_456, F_453) | ~v1_partfun1(F_453, A_454) | ~m1_subset_1(F_453, k1_zfmisc_1(k2_zfmisc_1(A_454, B_455))) | ~v1_funct_1(F_453) | ~m1_subset_1(C_456, k1_zfmisc_1(k2_zfmisc_1(A_454, B_455))) | ~v1_funct_1(C_456))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.68/1.87  tff(c_2295, plain, (![A_62, C_456]: (r2_hidden(k6_partfun1(A_62), k5_partfun1(A_62, A_62, C_456)) | ~r1_partfun1(C_456, k6_partfun1(A_62)) | ~v1_partfun1(k6_partfun1(A_62), A_62) | ~v1_funct_1(k6_partfun1(A_62)) | ~m1_subset_1(C_456, k1_zfmisc_1(k2_zfmisc_1(A_62, A_62))) | ~v1_funct_1(C_456))), inference(resolution, [status(thm)], [c_70, c_2287])).
% 4.68/1.87  tff(c_2373, plain, (![A_473, C_474]: (r2_hidden(k6_partfun1(A_473), k5_partfun1(A_473, A_473, C_474)) | ~r1_partfun1(C_474, k6_partfun1(A_473)) | ~v1_funct_1(k6_partfun1(A_473)) | ~m1_subset_1(C_474, k1_zfmisc_1(k2_zfmisc_1(A_473, A_473))) | ~v1_funct_1(C_474))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2295])).
% 4.68/1.87  tff(c_2382, plain, (![C_474]: (r2_hidden('#skF_8', k5_partfun1('#skF_8', '#skF_8', C_474)) | ~r1_partfun1(C_474, k6_partfun1('#skF_8')) | ~v1_funct_1(k6_partfun1('#skF_8')) | ~m1_subset_1(C_474, k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_8'))) | ~v1_funct_1(C_474))), inference(superposition, [status(thm), theory('equality')], [c_1604, c_2373])).
% 4.68/1.87  tff(c_2388, plain, (![C_475]: (r2_hidden('#skF_8', k5_partfun1('#skF_8', '#skF_8', C_475)) | ~r1_partfun1(C_475, '#skF_8') | ~m1_subset_1(C_475, k1_zfmisc_1('#skF_8')) | ~v1_funct_1(C_475))), inference(demodulation, [status(thm), theory('equality')], [c_1510, c_86, c_1604, c_1604, c_2382])).
% 4.68/1.87  tff(c_1485, plain, (~r2_hidden('#skF_9', k5_partfun1('#skF_6', '#skF_6', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1444, c_72])).
% 4.68/1.87  tff(c_1505, plain, (~r2_hidden('#skF_9', k5_partfun1('#skF_8', '#skF_8', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1503, c_1503, c_1485])).
% 4.68/1.87  tff(c_1620, plain, (~r2_hidden('#skF_8', k5_partfun1('#skF_8', '#skF_8', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1581, c_1505])).
% 4.68/1.87  tff(c_2397, plain, (~r1_partfun1('#skF_8', '#skF_8') | ~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8')) | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_2388, c_1620])).
% 4.68/1.87  tff(c_2405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_1506, c_1587, c_2397])).
% 4.68/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.68/1.87  
% 4.68/1.87  Inference rules
% 4.68/1.87  ----------------------
% 4.68/1.87  #Ref     : 0
% 4.68/1.87  #Sup     : 556
% 4.68/1.87  #Fact    : 0
% 4.68/1.87  #Define  : 0
% 4.68/1.87  #Split   : 13
% 4.68/1.87  #Chain   : 0
% 4.68/1.87  #Close   : 0
% 4.68/1.87  
% 4.68/1.87  Ordering : KBO
% 4.68/1.87  
% 4.68/1.87  Simplification rules
% 4.68/1.87  ----------------------
% 4.68/1.87  #Subsume      : 192
% 4.68/1.87  #Demod        : 290
% 4.68/1.87  #Tautology    : 101
% 4.68/1.87  #SimpNegUnit  : 18
% 4.68/1.87  #BackRed      : 22
% 4.68/1.87  
% 4.68/1.87  #Partial instantiations: 0
% 4.68/1.87  #Strategies tried      : 1
% 4.68/1.87  
% 4.68/1.87  Timing (in seconds)
% 4.68/1.87  ----------------------
% 4.68/1.87  Preprocessing        : 0.35
% 4.68/1.87  Parsing              : 0.17
% 4.68/1.87  CNF conversion       : 0.03
% 4.68/1.87  Main loop            : 0.74
% 4.68/1.87  Inferencing          : 0.25
% 4.68/1.87  Reduction            : 0.23
% 4.68/1.87  Demodulation         : 0.16
% 4.68/1.87  BG Simplification    : 0.03
% 4.68/1.88  Subsumption          : 0.17
% 4.68/1.88  Abstraction          : 0.03
% 4.68/1.88  MUC search           : 0.00
% 4.68/1.88  Cooper               : 0.00
% 4.68/1.88  Total                : 1.13
% 4.68/1.88  Index Insertion      : 0.00
% 4.68/1.88  Index Deletion       : 0.00
% 4.68/1.88  Index Matching       : 0.00
% 4.68/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
