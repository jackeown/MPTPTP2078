%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:02 EST 2020

% Result     : Theorem 13.32s
% Output     : CNFRefutation 13.32s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 623 expanded)
%              Number of leaves         :   35 ( 212 expanded)
%              Depth                    :   12
%              Number of atoms          :  188 (1761 expanded)
%              Number of equality atoms :   30 ( 586 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_1

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

tff(f_127,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_2)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_106,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_partfun1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

tff(c_74,plain,(
    ~ r2_hidden('#skF_9',k5_partfun1('#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_88,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_78,plain,(
    r1_partfun1('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_86,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_84,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_76,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_98,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_82,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_80,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_350,plain,(
    ! [C_124,A_125,B_126] :
      ( v1_partfun1(C_124,A_125)
      | ~ v1_funct_2(C_124,A_125,B_126)
      | ~ v1_funct_1(C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126)))
      | v1_xboole_0(B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_357,plain,
    ( v1_partfun1('#skF_9','#skF_6')
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7')
    | ~ v1_funct_1('#skF_9')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_80,c_350])).

tff(c_374,plain,
    ( v1_partfun1('#skF_9','#skF_6')
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_357])).

tff(c_380,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_374])).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_186,plain,(
    ! [C_91,B_92,A_93] :
      ( ~ v1_xboole_0(C_91)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(C_91))
      | ~ r2_hidden(A_93,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_209,plain,(
    ! [B_95,A_96,A_97] :
      ( ~ v1_xboole_0(B_95)
      | ~ r2_hidden(A_96,A_97)
      | ~ r1_tarski(A_97,B_95) ) ),
    inference(resolution,[status(thm)],[c_26,c_186])).

tff(c_213,plain,(
    ! [B_98,A_99,B_100] :
      ( ~ v1_xboole_0(B_98)
      | ~ r1_tarski(A_99,B_98)
      | r1_tarski(A_99,B_100) ) ),
    inference(resolution,[status(thm)],[c_6,c_209])).

tff(c_227,plain,(
    ! [B_101,B_102] :
      ( ~ v1_xboole_0(B_101)
      | r1_tarski(B_101,B_102) ) ),
    inference(resolution,[status(thm)],[c_14,c_213])).

tff(c_22,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_115,plain,(
    ! [A_74,B_75] :
      ( r1_tarski(A_74,B_75)
      | ~ m1_subset_1(A_74,k1_zfmisc_1(B_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_127,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(resolution,[status(thm)],[c_22,c_115])).

tff(c_134,plain,(
    ! [B_79,A_80] :
      ( B_79 = A_80
      | ~ r1_tarski(B_79,A_80)
      | ~ r1_tarski(A_80,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_145,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_127,c_134])).

tff(c_237,plain,(
    ! [B_101] :
      ( k1_xboole_0 = B_101
      | ~ v1_xboole_0(B_101) ) ),
    inference(resolution,[status(thm)],[c_227,c_145])).

tff(c_385,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_380,c_237])).

tff(c_390,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_385])).

tff(c_391,plain,(
    v1_partfun1('#skF_9','#skF_6') ),
    inference(splitRight,[status(thm)],[c_374])).

tff(c_1396,plain,(
    ! [F_230,A_231,B_232,C_233] :
      ( r2_hidden(F_230,k5_partfun1(A_231,B_232,C_233))
      | ~ r1_partfun1(C_233,F_230)
      | ~ v1_partfun1(F_230,A_231)
      | ~ m1_subset_1(F_230,k1_zfmisc_1(k2_zfmisc_1(A_231,B_232)))
      | ~ v1_funct_1(F_230)
      | ~ m1_subset_1(C_233,k1_zfmisc_1(k2_zfmisc_1(A_231,B_232)))
      | ~ v1_funct_1(C_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1404,plain,(
    ! [C_233] :
      ( r2_hidden('#skF_9',k5_partfun1('#skF_6','#skF_7',C_233))
      | ~ r1_partfun1(C_233,'#skF_9')
      | ~ v1_partfun1('#skF_9','#skF_6')
      | ~ v1_funct_1('#skF_9')
      | ~ m1_subset_1(C_233,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ v1_funct_1(C_233) ) ),
    inference(resolution,[status(thm)],[c_80,c_1396])).

tff(c_1551,plain,(
    ! [C_239] :
      ( r2_hidden('#skF_9',k5_partfun1('#skF_6','#skF_7',C_239))
      | ~ r1_partfun1(C_239,'#skF_9')
      | ~ m1_subset_1(C_239,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | ~ v1_funct_1(C_239) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_391,c_1404])).

tff(c_1565,plain,
    ( r2_hidden('#skF_9',k5_partfun1('#skF_6','#skF_7','#skF_8'))
    | ~ r1_partfun1('#skF_8','#skF_9')
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_86,c_1551])).

tff(c_1578,plain,(
    r2_hidden('#skF_9',k5_partfun1('#skF_6','#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_78,c_1565])).

tff(c_1580,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1578])).

tff(c_1581,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_1594,plain,(
    ! [A_10] : m1_subset_1('#skF_6',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1581,c_22])).

tff(c_1624,plain,(
    ! [A_245,B_246] :
      ( r1_tarski(A_245,B_246)
      | ~ m1_subset_1(A_245,k1_zfmisc_1(B_246)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1640,plain,(
    ! [A_10] : r1_tarski('#skF_6',A_10) ),
    inference(resolution,[status(thm)],[c_1594,c_1624])).

tff(c_20,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1583,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_6',B_9) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1581,c_1581,c_20])).

tff(c_1582,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_1589,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1581,c_1582])).

tff(c_1620,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1583,c_1589,c_86])).

tff(c_1639,plain,(
    r1_tarski('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_1620,c_1624])).

tff(c_1642,plain,(
    ! [B_248,A_249] :
      ( B_248 = A_249
      | ~ r1_tarski(B_248,A_249)
      | ~ r1_tarski(A_249,B_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1646,plain,
    ( '#skF_6' = '#skF_8'
    | ~ r1_tarski('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_1639,c_1642])).

tff(c_1654,plain,(
    '#skF_6' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1640,c_1646])).

tff(c_1662,plain,(
    ! [A_10] : r1_tarski('#skF_8',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1654,c_1640])).

tff(c_18,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1604,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1581,c_1581,c_18])).

tff(c_1668,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1654,c_1654,c_1604])).

tff(c_1671,plain,(
    ! [A_10] : m1_subset_1('#skF_8',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1654,c_1594])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1584,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1581,c_8])).

tff(c_1672,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1654,c_1584])).

tff(c_1669,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_8',B_9) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1654,c_1654,c_1583])).

tff(c_1851,plain,(
    ! [C_287,A_288,B_289] :
      ( v1_partfun1(C_287,A_288)
      | ~ m1_subset_1(C_287,k1_zfmisc_1(k2_zfmisc_1(A_288,B_289)))
      | ~ v1_xboole_0(A_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1861,plain,(
    ! [C_287] :
      ( v1_partfun1(C_287,'#skF_8')
      | ~ m1_subset_1(C_287,k1_zfmisc_1('#skF_8'))
      | ~ v1_xboole_0('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1669,c_1851])).

tff(c_1891,plain,(
    ! [C_294] :
      ( v1_partfun1(C_294,'#skF_8')
      | ~ m1_subset_1(C_294,k1_zfmisc_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1672,c_1861])).

tff(c_1900,plain,(
    v1_partfun1('#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_1671,c_1891])).

tff(c_1621,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1583,c_1589,c_80])).

tff(c_1638,plain,(
    r1_tarski('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_1621,c_1624])).

tff(c_1648,plain,
    ( '#skF_6' = '#skF_9'
    | ~ r1_tarski('#skF_6','#skF_9') ),
    inference(resolution,[status(thm)],[c_1638,c_1642])).

tff(c_1657,plain,(
    '#skF_6' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1640,c_1648])).

tff(c_1680,plain,(
    '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1654,c_1657])).

tff(c_1681,plain,(
    r1_partfun1('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1680,c_78])).

tff(c_2425,plain,(
    ! [F_368,A_369,B_370,C_371] :
      ( r2_hidden(F_368,k5_partfun1(A_369,B_370,C_371))
      | ~ r1_partfun1(C_371,F_368)
      | ~ v1_partfun1(F_368,A_369)
      | ~ m1_subset_1(F_368,k1_zfmisc_1(k2_zfmisc_1(A_369,B_370)))
      | ~ v1_funct_1(F_368)
      | ~ m1_subset_1(C_371,k1_zfmisc_1(k2_zfmisc_1(A_369,B_370)))
      | ~ v1_funct_1(C_371) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_6380,plain,(
    ! [A_579,A_580,B_581,C_582] :
      ( r2_hidden(A_579,k5_partfun1(A_580,B_581,C_582))
      | ~ r1_partfun1(C_582,A_579)
      | ~ v1_partfun1(A_579,A_580)
      | ~ v1_funct_1(A_579)
      | ~ m1_subset_1(C_582,k1_zfmisc_1(k2_zfmisc_1(A_580,B_581)))
      | ~ v1_funct_1(C_582)
      | ~ r1_tarski(A_579,k2_zfmisc_1(A_580,B_581)) ) ),
    inference(resolution,[status(thm)],[c_26,c_2425])).

tff(c_31859,plain,(
    ! [A_1082,A_1083,B_1084,A_1085] :
      ( r2_hidden(A_1082,k5_partfun1(A_1083,B_1084,A_1085))
      | ~ r1_partfun1(A_1085,A_1082)
      | ~ v1_partfun1(A_1082,A_1083)
      | ~ v1_funct_1(A_1082)
      | ~ v1_funct_1(A_1085)
      | ~ r1_tarski(A_1082,k2_zfmisc_1(A_1083,B_1084))
      | ~ r1_tarski(A_1085,k2_zfmisc_1(A_1083,B_1084)) ) ),
    inference(resolution,[status(thm)],[c_26,c_6380])).

tff(c_1622,plain,(
    ~ r2_hidden('#skF_9',k5_partfun1('#skF_6','#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1589,c_74])).

tff(c_1665,plain,(
    ~ r2_hidden('#skF_9',k5_partfun1('#skF_8','#skF_8','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1654,c_1654,c_1622])).

tff(c_1764,plain,(
    ~ r2_hidden('#skF_8',k5_partfun1('#skF_8','#skF_8','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1680,c_1665])).

tff(c_31903,plain,
    ( ~ r1_partfun1('#skF_8','#skF_8')
    | ~ v1_partfun1('#skF_8','#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ r1_tarski('#skF_8',k2_zfmisc_1('#skF_8','#skF_8')) ),
    inference(resolution,[status(thm)],[c_31859,c_1764])).

tff(c_31925,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1662,c_1668,c_88,c_1900,c_1681,c_31903])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:31:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.32/6.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.32/6.36  
% 13.32/6.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.32/6.36  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_1
% 13.32/6.36  
% 13.32/6.36  %Foreground sorts:
% 13.32/6.36  
% 13.32/6.36  
% 13.32/6.36  %Background operators:
% 13.32/6.36  
% 13.32/6.36  
% 13.32/6.36  %Foreground operators:
% 13.32/6.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.32/6.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.32/6.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.32/6.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.32/6.36  tff('#skF_7', type, '#skF_7': $i).
% 13.32/6.36  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i) > $i).
% 13.32/6.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.32/6.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.32/6.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 13.32/6.36  tff('#skF_6', type, '#skF_6': $i).
% 13.32/6.36  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 13.32/6.36  tff('#skF_9', type, '#skF_9': $i).
% 13.32/6.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.32/6.36  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 13.32/6.36  tff('#skF_8', type, '#skF_8': $i).
% 13.32/6.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.32/6.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.32/6.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.32/6.36  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 13.32/6.36  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 13.32/6.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.32/6.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.32/6.36  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 13.32/6.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.32/6.36  
% 13.32/6.38  tff(f_127, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_hidden(D, k5_partfun1(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_2)).
% 13.32/6.38  tff(f_85, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 13.32/6.38  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.32/6.38  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 13.32/6.38  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 13.32/6.38  tff(f_64, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 13.32/6.38  tff(f_47, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 13.32/6.38  tff(f_106, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((D = k5_partfun1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> (?[F]: ((((v1_funct_1(F) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & (F = E)) & v1_partfun1(F, A)) & r1_partfun1(C, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_partfun1)).
% 13.32/6.38  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 13.32/6.38  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 13.32/6.38  tff(f_71, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 13.32/6.38  tff(c_74, plain, (~r2_hidden('#skF_9', k5_partfun1('#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.32/6.38  tff(c_88, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.32/6.38  tff(c_78, plain, (r1_partfun1('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.32/6.38  tff(c_86, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.32/6.38  tff(c_84, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.32/6.38  tff(c_76, plain, (k1_xboole_0='#skF_6' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.32/6.38  tff(c_98, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_76])).
% 13.32/6.38  tff(c_82, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.32/6.38  tff(c_80, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.32/6.38  tff(c_350, plain, (![C_124, A_125, B_126]: (v1_partfun1(C_124, A_125) | ~v1_funct_2(C_124, A_125, B_126) | ~v1_funct_1(C_124) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))) | v1_xboole_0(B_126))), inference(cnfTransformation, [status(thm)], [f_85])).
% 13.32/6.38  tff(c_357, plain, (v1_partfun1('#skF_9', '#skF_6') | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7') | ~v1_funct_1('#skF_9') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_80, c_350])).
% 13.32/6.38  tff(c_374, plain, (v1_partfun1('#skF_9', '#skF_6') | v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_357])).
% 13.32/6.38  tff(c_380, plain, (v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_374])).
% 13.32/6.38  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.32/6.38  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.32/6.38  tff(c_26, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.32/6.38  tff(c_186, plain, (![C_91, B_92, A_93]: (~v1_xboole_0(C_91) | ~m1_subset_1(B_92, k1_zfmisc_1(C_91)) | ~r2_hidden(A_93, B_92))), inference(cnfTransformation, [status(thm)], [f_64])).
% 13.32/6.38  tff(c_209, plain, (![B_95, A_96, A_97]: (~v1_xboole_0(B_95) | ~r2_hidden(A_96, A_97) | ~r1_tarski(A_97, B_95))), inference(resolution, [status(thm)], [c_26, c_186])).
% 13.32/6.38  tff(c_213, plain, (![B_98, A_99, B_100]: (~v1_xboole_0(B_98) | ~r1_tarski(A_99, B_98) | r1_tarski(A_99, B_100))), inference(resolution, [status(thm)], [c_6, c_209])).
% 13.32/6.38  tff(c_227, plain, (![B_101, B_102]: (~v1_xboole_0(B_101) | r1_tarski(B_101, B_102))), inference(resolution, [status(thm)], [c_14, c_213])).
% 13.32/6.38  tff(c_22, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.32/6.38  tff(c_115, plain, (![A_74, B_75]: (r1_tarski(A_74, B_75) | ~m1_subset_1(A_74, k1_zfmisc_1(B_75)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.32/6.38  tff(c_127, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(resolution, [status(thm)], [c_22, c_115])).
% 13.32/6.38  tff(c_134, plain, (![B_79, A_80]: (B_79=A_80 | ~r1_tarski(B_79, A_80) | ~r1_tarski(A_80, B_79))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.32/6.38  tff(c_145, plain, (![A_10]: (k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_xboole_0))), inference(resolution, [status(thm)], [c_127, c_134])).
% 13.32/6.38  tff(c_237, plain, (![B_101]: (k1_xboole_0=B_101 | ~v1_xboole_0(B_101))), inference(resolution, [status(thm)], [c_227, c_145])).
% 13.32/6.38  tff(c_385, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_380, c_237])).
% 13.32/6.38  tff(c_390, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_385])).
% 13.32/6.38  tff(c_391, plain, (v1_partfun1('#skF_9', '#skF_6')), inference(splitRight, [status(thm)], [c_374])).
% 13.32/6.38  tff(c_1396, plain, (![F_230, A_231, B_232, C_233]: (r2_hidden(F_230, k5_partfun1(A_231, B_232, C_233)) | ~r1_partfun1(C_233, F_230) | ~v1_partfun1(F_230, A_231) | ~m1_subset_1(F_230, k1_zfmisc_1(k2_zfmisc_1(A_231, B_232))) | ~v1_funct_1(F_230) | ~m1_subset_1(C_233, k1_zfmisc_1(k2_zfmisc_1(A_231, B_232))) | ~v1_funct_1(C_233))), inference(cnfTransformation, [status(thm)], [f_106])).
% 13.32/6.38  tff(c_1404, plain, (![C_233]: (r2_hidden('#skF_9', k5_partfun1('#skF_6', '#skF_7', C_233)) | ~r1_partfun1(C_233, '#skF_9') | ~v1_partfun1('#skF_9', '#skF_6') | ~v1_funct_1('#skF_9') | ~m1_subset_1(C_233, k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~v1_funct_1(C_233))), inference(resolution, [status(thm)], [c_80, c_1396])).
% 13.32/6.38  tff(c_1551, plain, (![C_239]: (r2_hidden('#skF_9', k5_partfun1('#skF_6', '#skF_7', C_239)) | ~r1_partfun1(C_239, '#skF_9') | ~m1_subset_1(C_239, k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | ~v1_funct_1(C_239))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_391, c_1404])).
% 13.32/6.38  tff(c_1565, plain, (r2_hidden('#skF_9', k5_partfun1('#skF_6', '#skF_7', '#skF_8')) | ~r1_partfun1('#skF_8', '#skF_9') | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_86, c_1551])).
% 13.32/6.38  tff(c_1578, plain, (r2_hidden('#skF_9', k5_partfun1('#skF_6', '#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_78, c_1565])).
% 13.32/6.38  tff(c_1580, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_1578])).
% 13.32/6.38  tff(c_1581, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_76])).
% 13.32/6.38  tff(c_1594, plain, (![A_10]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_1581, c_22])).
% 13.32/6.38  tff(c_1624, plain, (![A_245, B_246]: (r1_tarski(A_245, B_246) | ~m1_subset_1(A_245, k1_zfmisc_1(B_246)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.32/6.38  tff(c_1640, plain, (![A_10]: (r1_tarski('#skF_6', A_10))), inference(resolution, [status(thm)], [c_1594, c_1624])).
% 13.32/6.38  tff(c_20, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.32/6.38  tff(c_1583, plain, (![B_9]: (k2_zfmisc_1('#skF_6', B_9)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1581, c_1581, c_20])).
% 13.32/6.38  tff(c_1582, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_76])).
% 13.32/6.38  tff(c_1589, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1581, c_1582])).
% 13.32/6.38  tff(c_1620, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1583, c_1589, c_86])).
% 13.32/6.38  tff(c_1639, plain, (r1_tarski('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_1620, c_1624])).
% 13.32/6.38  tff(c_1642, plain, (![B_248, A_249]: (B_248=A_249 | ~r1_tarski(B_248, A_249) | ~r1_tarski(A_249, B_248))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.32/6.38  tff(c_1646, plain, ('#skF_6'='#skF_8' | ~r1_tarski('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_1639, c_1642])).
% 13.32/6.38  tff(c_1654, plain, ('#skF_6'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1640, c_1646])).
% 13.32/6.38  tff(c_1662, plain, (![A_10]: (r1_tarski('#skF_8', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_1654, c_1640])).
% 13.32/6.38  tff(c_18, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.32/6.38  tff(c_1604, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1581, c_1581, c_18])).
% 13.32/6.38  tff(c_1668, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1654, c_1654, c_1604])).
% 13.32/6.38  tff(c_1671, plain, (![A_10]: (m1_subset_1('#skF_8', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_1654, c_1594])).
% 13.32/6.38  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.32/6.38  tff(c_1584, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1581, c_8])).
% 13.32/6.38  tff(c_1672, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1654, c_1584])).
% 13.32/6.38  tff(c_1669, plain, (![B_9]: (k2_zfmisc_1('#skF_8', B_9)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1654, c_1654, c_1583])).
% 13.32/6.38  tff(c_1851, plain, (![C_287, A_288, B_289]: (v1_partfun1(C_287, A_288) | ~m1_subset_1(C_287, k1_zfmisc_1(k2_zfmisc_1(A_288, B_289))) | ~v1_xboole_0(A_288))), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.32/6.38  tff(c_1861, plain, (![C_287]: (v1_partfun1(C_287, '#skF_8') | ~m1_subset_1(C_287, k1_zfmisc_1('#skF_8')) | ~v1_xboole_0('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1669, c_1851])).
% 13.32/6.38  tff(c_1891, plain, (![C_294]: (v1_partfun1(C_294, '#skF_8') | ~m1_subset_1(C_294, k1_zfmisc_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_1672, c_1861])).
% 13.32/6.38  tff(c_1900, plain, (v1_partfun1('#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_1671, c_1891])).
% 13.32/6.38  tff(c_1621, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1583, c_1589, c_80])).
% 13.32/6.38  tff(c_1638, plain, (r1_tarski('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_1621, c_1624])).
% 13.32/6.38  tff(c_1648, plain, ('#skF_6'='#skF_9' | ~r1_tarski('#skF_6', '#skF_9')), inference(resolution, [status(thm)], [c_1638, c_1642])).
% 13.32/6.38  tff(c_1657, plain, ('#skF_6'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1640, c_1648])).
% 13.32/6.38  tff(c_1680, plain, ('#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1654, c_1657])).
% 13.32/6.38  tff(c_1681, plain, (r1_partfun1('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1680, c_78])).
% 13.32/6.38  tff(c_2425, plain, (![F_368, A_369, B_370, C_371]: (r2_hidden(F_368, k5_partfun1(A_369, B_370, C_371)) | ~r1_partfun1(C_371, F_368) | ~v1_partfun1(F_368, A_369) | ~m1_subset_1(F_368, k1_zfmisc_1(k2_zfmisc_1(A_369, B_370))) | ~v1_funct_1(F_368) | ~m1_subset_1(C_371, k1_zfmisc_1(k2_zfmisc_1(A_369, B_370))) | ~v1_funct_1(C_371))), inference(cnfTransformation, [status(thm)], [f_106])).
% 13.32/6.38  tff(c_6380, plain, (![A_579, A_580, B_581, C_582]: (r2_hidden(A_579, k5_partfun1(A_580, B_581, C_582)) | ~r1_partfun1(C_582, A_579) | ~v1_partfun1(A_579, A_580) | ~v1_funct_1(A_579) | ~m1_subset_1(C_582, k1_zfmisc_1(k2_zfmisc_1(A_580, B_581))) | ~v1_funct_1(C_582) | ~r1_tarski(A_579, k2_zfmisc_1(A_580, B_581)))), inference(resolution, [status(thm)], [c_26, c_2425])).
% 13.32/6.38  tff(c_31859, plain, (![A_1082, A_1083, B_1084, A_1085]: (r2_hidden(A_1082, k5_partfun1(A_1083, B_1084, A_1085)) | ~r1_partfun1(A_1085, A_1082) | ~v1_partfun1(A_1082, A_1083) | ~v1_funct_1(A_1082) | ~v1_funct_1(A_1085) | ~r1_tarski(A_1082, k2_zfmisc_1(A_1083, B_1084)) | ~r1_tarski(A_1085, k2_zfmisc_1(A_1083, B_1084)))), inference(resolution, [status(thm)], [c_26, c_6380])).
% 13.32/6.38  tff(c_1622, plain, (~r2_hidden('#skF_9', k5_partfun1('#skF_6', '#skF_6', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1589, c_74])).
% 13.32/6.38  tff(c_1665, plain, (~r2_hidden('#skF_9', k5_partfun1('#skF_8', '#skF_8', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1654, c_1654, c_1622])).
% 13.32/6.38  tff(c_1764, plain, (~r2_hidden('#skF_8', k5_partfun1('#skF_8', '#skF_8', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1680, c_1665])).
% 13.32/6.38  tff(c_31903, plain, (~r1_partfun1('#skF_8', '#skF_8') | ~v1_partfun1('#skF_8', '#skF_8') | ~v1_funct_1('#skF_8') | ~r1_tarski('#skF_8', k2_zfmisc_1('#skF_8', '#skF_8'))), inference(resolution, [status(thm)], [c_31859, c_1764])).
% 13.32/6.38  tff(c_31925, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1662, c_1668, c_88, c_1900, c_1681, c_31903])).
% 13.32/6.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.32/6.38  
% 13.32/6.38  Inference rules
% 13.32/6.38  ----------------------
% 13.32/6.38  #Ref     : 0
% 13.32/6.38  #Sup     : 8510
% 13.32/6.38  #Fact    : 6
% 13.32/6.38  #Define  : 0
% 13.32/6.38  #Split   : 26
% 13.32/6.38  #Chain   : 0
% 13.32/6.38  #Close   : 0
% 13.32/6.38  
% 13.32/6.38  Ordering : KBO
% 13.32/6.38  
% 13.32/6.38  Simplification rules
% 13.32/6.38  ----------------------
% 13.32/6.38  #Subsume      : 5208
% 13.32/6.38  #Demod        : 1560
% 13.32/6.38  #Tautology    : 1355
% 13.32/6.38  #SimpNegUnit  : 110
% 13.32/6.38  #BackRed      : 64
% 13.32/6.38  
% 13.32/6.38  #Partial instantiations: 0
% 13.32/6.38  #Strategies tried      : 1
% 13.32/6.38  
% 13.32/6.38  Timing (in seconds)
% 13.32/6.38  ----------------------
% 13.32/6.38  Preprocessing        : 0.34
% 13.32/6.38  Parsing              : 0.17
% 13.32/6.38  CNF conversion       : 0.03
% 13.32/6.38  Main loop            : 5.27
% 13.32/6.38  Inferencing          : 1.03
% 13.32/6.38  Reduction            : 1.04
% 13.32/6.38  Demodulation         : 0.71
% 13.32/6.38  BG Simplification    : 0.12
% 13.32/6.38  Subsumption          : 2.82
% 13.32/6.38  Abstraction          : 0.17
% 13.32/6.38  MUC search           : 0.00
% 13.32/6.38  Cooper               : 0.00
% 13.32/6.38  Total                : 5.65
% 13.32/6.38  Index Insertion      : 0.00
% 13.32/6.39  Index Deletion       : 0.00
% 13.32/6.39  Index Matching       : 0.00
% 13.32/6.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
