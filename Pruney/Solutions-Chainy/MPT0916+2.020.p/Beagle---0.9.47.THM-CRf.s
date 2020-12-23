%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:13 EST 2020

% Result     : Theorem 4.97s
% Output     : CNFRefutation 5.31s
% Verified   : 
% Statistics : Number of formulae       :  199 ( 566 expanded)
%              Number of leaves         :   34 ( 192 expanded)
%              Depth                    :    9
%              Number of atoms          :  304 (1603 expanded)
%              Number of equality atoms :  103 ( 474 expanded)
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

tff(f_105,negated_conjecture,(
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

tff(f_57,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_59,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_85,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_38,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_38,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1628,plain,(
    ! [C_332,B_333,A_334] :
      ( ~ v1_xboole_0(C_332)
      | ~ m1_subset_1(B_333,k1_zfmisc_1(C_332))
      | ~ r2_hidden(A_334,B_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1638,plain,(
    ! [A_334] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_334,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_38,c_1628])).

tff(c_1651,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1638])).

tff(c_34,plain,(
    r2_hidden('#skF_8',k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1609,plain,(
    ! [A_329,B_330,C_331] : k2_zfmisc_1(k2_zfmisc_1(A_329,B_330),C_331) = k3_zfmisc_1(A_329,B_330,C_331) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_22,plain,(
    ! [A_19,C_21,B_20] :
      ( r2_hidden(k2_mcart_1(A_19),C_21)
      | ~ r2_hidden(A_19,k2_zfmisc_1(B_20,C_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1767,plain,(
    ! [A_360,C_361,A_362,B_363] :
      ( r2_hidden(k2_mcart_1(A_360),C_361)
      | ~ r2_hidden(A_360,k3_zfmisc_1(A_362,B_363,C_361)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1609,c_22])).

tff(c_1778,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_34,c_1767])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1639,plain,(
    ! [A_334] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_334,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40,c_1628])).

tff(c_1653,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1639])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1640,plain,(
    ! [A_334] :
      ( ~ v1_xboole_0('#skF_2')
      | ~ r2_hidden(A_334,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_42,c_1628])).

tff(c_1652,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1640])).

tff(c_36,plain,(
    m1_subset_1('#skF_8',k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1674,plain,(
    ! [A_342,B_343,C_344,D_345] :
      ( k7_mcart_1(A_342,B_343,C_344,D_345) = k2_mcart_1(D_345)
      | ~ m1_subset_1(D_345,k3_zfmisc_1(A_342,B_343,C_344))
      | k1_xboole_0 = C_344
      | k1_xboole_0 = B_343
      | k1_xboole_0 = A_342 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1678,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_1674])).

tff(c_1800,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1678])).

tff(c_1585,plain,(
    ! [A_320,B_321] :
      ( r2_hidden('#skF_1'(A_320,B_321),A_320)
      | r1_tarski(A_320,B_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1591,plain,(
    ! [A_322] : r1_tarski(A_322,A_322) ),
    inference(resolution,[status(thm)],[c_1585,c_4])).

tff(c_10,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1575,plain,(
    ! [B_317,A_318] :
      ( ~ r1_xboole_0(B_317,A_318)
      | ~ r1_tarski(B_317,A_318)
      | v1_xboole_0(B_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1583,plain,(
    ! [A_8] :
      ( ~ r1_tarski(A_8,k1_xboole_0)
      | v1_xboole_0(A_8) ) ),
    inference(resolution,[status(thm)],[c_10,c_1575])).

tff(c_1596,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1591,c_1583])).

tff(c_1803,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1800,c_1596])).

tff(c_1808,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1652,c_1803])).

tff(c_1810,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1678])).

tff(c_1762,plain,(
    ! [A_356,B_357,C_358,D_359] :
      ( k6_mcart_1(A_356,B_357,C_358,D_359) = k2_mcart_1(k1_mcart_1(D_359))
      | ~ m1_subset_1(D_359,k3_zfmisc_1(A_356,B_357,C_358))
      | k1_xboole_0 = C_358
      | k1_xboole_0 = B_357
      | k1_xboole_0 = A_356 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1766,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_1762])).

tff(c_1869,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1810,c_1766])).

tff(c_1870,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1869])).

tff(c_1875,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1870,c_1596])).

tff(c_1880,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1653,c_1875])).

tff(c_1882,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1869])).

tff(c_1809,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_1678])).

tff(c_2009,plain,
    ( k1_xboole_0 = '#skF_4'
    | k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_1882,c_1809])).

tff(c_2010,plain,(
    k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_2009])).

tff(c_131,plain,(
    ! [C_63,B_64,A_65] :
      ( ~ v1_xboole_0(C_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(C_63))
      | ~ r2_hidden(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_141,plain,(
    ! [A_65] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_65,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_38,c_131])).

tff(c_144,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_141])).

tff(c_32,plain,
    ( ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7')
    | ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6')
    | ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_66,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_142,plain,(
    ! [A_65] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_65,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40,c_131])).

tff(c_145,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_143,plain,(
    ! [A_65] :
      ( ~ v1_xboole_0('#skF_2')
      | ~ r2_hidden(A_65,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_42,c_131])).

tff(c_146,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_143])).

tff(c_228,plain,(
    ! [A_89,B_90,C_91,D_92] :
      ( k7_mcart_1(A_89,B_90,C_91,D_92) = k2_mcart_1(D_92)
      | ~ m1_subset_1(D_92,k3_zfmisc_1(A_89,B_90,C_91))
      | k1_xboole_0 = C_91
      | k1_xboole_0 = B_90
      | k1_xboole_0 = A_89 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_232,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_228])).

tff(c_254,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_232])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_85,plain,(
    ! [A_52,B_53] :
      ( ~ r2_hidden('#skF_1'(A_52,B_53),B_53)
      | r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_91,plain,(
    ! [A_54] : r1_tarski(A_54,A_54) ),
    inference(resolution,[status(thm)],[c_6,c_85])).

tff(c_44,plain,(
    ! [B_39,A_40] :
      ( r1_xboole_0(B_39,A_40)
      | ~ r1_xboole_0(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_47,plain,(
    ! [A_8] : r1_xboole_0(k1_xboole_0,A_8) ),
    inference(resolution,[status(thm)],[c_10,c_44])).

tff(c_72,plain,(
    ! [B_46,A_47] :
      ( ~ r1_xboole_0(B_46,A_47)
      | ~ r1_tarski(B_46,A_47)
      | v1_xboole_0(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_79,plain,(
    ! [A_8] :
      ( ~ r1_tarski(k1_xboole_0,A_8)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_47,c_72])).

tff(c_82,plain,(
    ! [A_8] : ~ r1_tarski(k1_xboole_0,A_8) ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_100,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_91,c_82])).

tff(c_101,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_256,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_101])).

tff(c_261,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_256])).

tff(c_263,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_232])).

tff(c_379,plain,(
    ! [A_107,B_108,C_109,D_110] :
      ( k5_mcart_1(A_107,B_108,C_109,D_110) = k1_mcart_1(k1_mcart_1(D_110))
      | ~ m1_subset_1(D_110,k3_zfmisc_1(A_107,B_108,C_109))
      | k1_xboole_0 = C_109
      | k1_xboole_0 = B_108
      | k1_xboole_0 = A_107 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_382,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_379])).

tff(c_385,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_263,c_382])).

tff(c_495,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_385])).

tff(c_500,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_495,c_101])).

tff(c_505,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_500])).

tff(c_506,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_385])).

tff(c_508,plain,(
    k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_506])).

tff(c_20,plain,(
    ! [A_16,B_17,C_18] : k2_zfmisc_1(k2_zfmisc_1(A_16,B_17),C_18) = k3_zfmisc_1(A_16,B_17,C_18) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_201,plain,(
    ! [A_81,B_82,C_83] :
      ( r2_hidden(k1_mcart_1(A_81),B_82)
      | ~ r2_hidden(A_81,k2_zfmisc_1(B_82,C_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_518,plain,(
    ! [A_131,A_132,B_133,C_134] :
      ( r2_hidden(k1_mcart_1(A_131),k2_zfmisc_1(A_132,B_133))
      | ~ r2_hidden(A_131,k3_zfmisc_1(A_132,B_133,C_134)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_201])).

tff(c_537,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_34,c_518])).

tff(c_24,plain,(
    ! [A_19,B_20,C_21] :
      ( r2_hidden(k1_mcart_1(A_19),B_20)
      | ~ r2_hidden(A_19,k2_zfmisc_1(B_20,C_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_539,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_537,c_24])).

tff(c_547,plain,(
    r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_508,c_539])).

tff(c_549,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_547])).

tff(c_550,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_506])).

tff(c_557,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_550,c_101])).

tff(c_562,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_557])).

tff(c_563,plain,(
    ! [A_65] : ~ r2_hidden(A_65,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_143])).

tff(c_608,plain,(
    ! [A_145,B_146,C_147] :
      ( r2_hidden(k1_mcart_1(A_145),B_146)
      | ~ r2_hidden(A_145,k2_zfmisc_1(B_146,C_147)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_998,plain,(
    ! [A_210,A_211,B_212,C_213] :
      ( r2_hidden(k1_mcart_1(A_210),k2_zfmisc_1(A_211,B_212))
      | ~ r2_hidden(A_210,k3_zfmisc_1(A_211,B_212,C_213)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_608])).

tff(c_1017,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_34,c_998])).

tff(c_1023,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_1017,c_24])).

tff(c_1031,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_563,c_1023])).

tff(c_1032,plain,(
    ! [A_65] : ~ r2_hidden(A_65,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_1085,plain,(
    ! [A_227,B_228,C_229] :
      ( r2_hidden(k1_mcart_1(A_227),B_228)
      | ~ r2_hidden(A_227,k2_zfmisc_1(B_228,C_229)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1425,plain,(
    ! [A_280,A_281,B_282,C_283] :
      ( r2_hidden(k1_mcart_1(A_280),k2_zfmisc_1(A_281,B_282))
      | ~ r2_hidden(A_280,k3_zfmisc_1(A_281,B_282,C_283)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1085])).

tff(c_1444,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_34,c_1425])).

tff(c_1452,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_1444,c_22])).

tff(c_1459,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1032,c_1452])).

tff(c_1460,plain,(
    ! [A_65] : ~ r2_hidden(A_65,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_1532,plain,(
    ! [A_301,C_302,B_303] :
      ( r2_hidden(k2_mcart_1(A_301),C_302)
      | ~ r2_hidden(A_301,k2_zfmisc_1(B_303,C_302)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1556,plain,(
    ! [A_309,C_310,A_311,B_312] :
      ( r2_hidden(k2_mcart_1(A_309),C_310)
      | ~ r2_hidden(A_309,k3_zfmisc_1(A_311,B_312,C_310)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1532])).

tff(c_1561,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_34,c_1556])).

tff(c_1566,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1460,c_1561])).

tff(c_1567,plain,
    ( ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6')
    | ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1598,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1567])).

tff(c_2011,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2010,c_1598])).

tff(c_2014,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1778,c_2011])).

tff(c_2015,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2009])).

tff(c_2022,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2015,c_1596])).

tff(c_2027,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1651,c_2022])).

tff(c_2028,plain,(
    ! [A_334] : ~ r2_hidden(A_334,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1639])).

tff(c_2565,plain,(
    ! [A_465,A_466,B_467,C_468] :
      ( r2_hidden(k1_mcart_1(A_465),k2_zfmisc_1(A_466,B_467))
      | ~ r2_hidden(A_465,k3_zfmisc_1(A_466,B_467,C_468)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1609,c_24])).

tff(c_2591,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_34,c_2565])).

tff(c_2599,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_2591,c_22])).

tff(c_2606,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2028,c_2599])).

tff(c_2607,plain,(
    ! [A_334] : ~ r2_hidden(A_334,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_1640])).

tff(c_1568,plain,(
    r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_2610,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2607,c_1568])).

tff(c_2611,plain,(
    ! [A_334] : ~ r2_hidden(A_334,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_1638])).

tff(c_2709,plain,(
    ! [A_490,C_491,A_492,B_493] :
      ( r2_hidden(k2_mcart_1(A_490),C_491)
      | ~ r2_hidden(A_490,k3_zfmisc_1(A_492,B_493,C_491)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1609,c_22])).

tff(c_2714,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_34,c_2709])).

tff(c_2719,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2611,c_2714])).

tff(c_2720,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1567])).

tff(c_2722,plain,(
    ! [C_494,B_495,A_496] :
      ( ~ v1_xboole_0(C_494)
      | ~ m1_subset_1(B_495,k1_zfmisc_1(C_494))
      | ~ r2_hidden(A_496,B_495) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2732,plain,(
    ! [A_496] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_496,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_38,c_2722])).

tff(c_2735,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2732])).

tff(c_2733,plain,(
    ! [A_496] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_496,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40,c_2722])).

tff(c_2736,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2733])).

tff(c_2734,plain,(
    ! [A_496] :
      ( ~ v1_xboole_0('#skF_2')
      | ~ r2_hidden(A_496,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_42,c_2722])).

tff(c_2752,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2734])).

tff(c_2919,plain,(
    ! [A_528,B_529,C_530,D_531] :
      ( k7_mcart_1(A_528,B_529,C_530,D_531) = k2_mcart_1(D_531)
      | ~ m1_subset_1(D_531,k3_zfmisc_1(A_528,B_529,C_530))
      | k1_xboole_0 = C_530
      | k1_xboole_0 = B_529
      | k1_xboole_0 = A_528 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2923,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_2919])).

tff(c_2980,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2923])).

tff(c_2982,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2980,c_1596])).

tff(c_2987,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2752,c_2982])).

tff(c_2989,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2923])).

tff(c_3025,plain,(
    ! [A_539,B_540,C_541,D_542] :
      ( k5_mcart_1(A_539,B_540,C_541,D_542) = k1_mcart_1(k1_mcart_1(D_542))
      | ~ m1_subset_1(D_542,k3_zfmisc_1(A_539,B_540,C_541))
      | k1_xboole_0 = C_541
      | k1_xboole_0 = B_540
      | k1_xboole_0 = A_539 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3028,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_3025])).

tff(c_3031,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_2989,c_3028])).

tff(c_3218,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3031])).

tff(c_3223,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3218,c_1596])).

tff(c_3228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2736,c_3223])).

tff(c_3230,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3031])).

tff(c_3092,plain,(
    ! [A_548,B_549,C_550,D_551] :
      ( k6_mcart_1(A_548,B_549,C_550,D_551) = k2_mcart_1(k1_mcart_1(D_551))
      | ~ m1_subset_1(D_551,k3_zfmisc_1(A_548,B_549,C_550))
      | k1_xboole_0 = C_550
      | k1_xboole_0 = B_549
      | k1_xboole_0 = A_548 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3095,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_3092])).

tff(c_3098,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_2989,c_3095])).

tff(c_3316,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_3230,c_3098])).

tff(c_3317,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3316])).

tff(c_3323,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3317,c_1596])).

tff(c_3328,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2735,c_3323])).

tff(c_3329,plain,(
    k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_3316])).

tff(c_2792,plain,(
    ! [A_506,B_507,C_508] :
      ( r2_hidden(k1_mcart_1(A_506),B_507)
      | ~ r2_hidden(A_506,k2_zfmisc_1(B_507,C_508)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3244,plain,(
    ! [A_577,A_578,B_579,C_580] :
      ( r2_hidden(k1_mcart_1(A_577),k2_zfmisc_1(A_578,B_579))
      | ~ r2_hidden(A_577,k3_zfmisc_1(A_578,B_579,C_580)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2792])).

tff(c_3270,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_34,c_3244])).

tff(c_3279,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_3270,c_22])).

tff(c_3356,plain,(
    r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3329,c_3279])).

tff(c_3358,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2720,c_3356])).

tff(c_3359,plain,(
    ! [A_496] : ~ r2_hidden(A_496,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_2734])).

tff(c_3362,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3359,c_1568])).

tff(c_3363,plain,(
    ! [A_496] : ~ r2_hidden(A_496,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_2733])).

tff(c_3478,plain,(
    ! [A_603,B_604,C_605] :
      ( r2_hidden(k1_mcart_1(A_603),B_604)
      | ~ r2_hidden(A_603,k2_zfmisc_1(B_604,C_605)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3899,plain,(
    ! [A_657,A_658,B_659,C_660] :
      ( r2_hidden(k1_mcart_1(A_657),k2_zfmisc_1(A_658,B_659))
      | ~ r2_hidden(A_657,k3_zfmisc_1(A_658,B_659,C_660)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_3478])).

tff(c_3926,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_34,c_3899])).

tff(c_3932,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_3926,c_22])).

tff(c_3940,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3363,c_3932])).

tff(c_3941,plain,(
    ! [A_496] : ~ r2_hidden(A_496,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_2732])).

tff(c_2721,plain,(
    r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_1567])).

tff(c_3944,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3941,c_2721])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:44:30 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.97/1.94  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.97/1.96  
% 4.97/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.97/1.96  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1
% 4.97/1.96  
% 4.97/1.96  %Foreground sorts:
% 4.97/1.96  
% 4.97/1.96  
% 4.97/1.96  %Background operators:
% 4.97/1.96  
% 4.97/1.96  
% 4.97/1.96  %Foreground operators:
% 4.97/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.97/1.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.97/1.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.97/1.96  tff('#skF_7', type, '#skF_7': $i).
% 4.97/1.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.97/1.96  tff('#skF_5', type, '#skF_5': $i).
% 4.97/1.96  tff('#skF_6', type, '#skF_6': $i).
% 4.97/1.96  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.97/1.96  tff('#skF_2', type, '#skF_2': $i).
% 4.97/1.96  tff('#skF_3', type, '#skF_3': $i).
% 4.97/1.96  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 4.97/1.96  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 4.97/1.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.97/1.96  tff('#skF_8', type, '#skF_8': $i).
% 4.97/1.96  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 4.97/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.97/1.96  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 4.97/1.96  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.97/1.96  tff('#skF_4', type, '#skF_4': $i).
% 4.97/1.96  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 4.97/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.97/1.96  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 4.97/1.96  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.97/1.96  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.97/1.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.97/1.96  
% 5.31/1.99  tff(f_105, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (![F]: (m1_subset_1(F, k1_zfmisc_1(C)) => (![G]: (m1_subset_1(G, k3_zfmisc_1(A, B, C)) => (r2_hidden(G, k3_zfmisc_1(D, E, F)) => ((r2_hidden(k5_mcart_1(A, B, C, G), D) & r2_hidden(k6_mcart_1(A, B, C, G), E)) & r2_hidden(k7_mcart_1(A, B, C, G), F))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_mcart_1)).
% 5.31/1.99  tff(f_57, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 5.31/1.99  tff(f_59, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 5.31/1.99  tff(f_65, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 5.31/1.99  tff(f_85, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 5.31/1.99  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.31/1.99  tff(f_38, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.31/1.99  tff(f_46, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 5.31/1.99  tff(f_36, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 5.31/1.99  tff(c_38, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.31/1.99  tff(c_1628, plain, (![C_332, B_333, A_334]: (~v1_xboole_0(C_332) | ~m1_subset_1(B_333, k1_zfmisc_1(C_332)) | ~r2_hidden(A_334, B_333))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.31/1.99  tff(c_1638, plain, (![A_334]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_334, '#skF_7'))), inference(resolution, [status(thm)], [c_38, c_1628])).
% 5.31/1.99  tff(c_1651, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_1638])).
% 5.31/1.99  tff(c_34, plain, (r2_hidden('#skF_8', k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.31/1.99  tff(c_1609, plain, (![A_329, B_330, C_331]: (k2_zfmisc_1(k2_zfmisc_1(A_329, B_330), C_331)=k3_zfmisc_1(A_329, B_330, C_331))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.31/1.99  tff(c_22, plain, (![A_19, C_21, B_20]: (r2_hidden(k2_mcart_1(A_19), C_21) | ~r2_hidden(A_19, k2_zfmisc_1(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.31/1.99  tff(c_1767, plain, (![A_360, C_361, A_362, B_363]: (r2_hidden(k2_mcart_1(A_360), C_361) | ~r2_hidden(A_360, k3_zfmisc_1(A_362, B_363, C_361)))), inference(superposition, [status(thm), theory('equality')], [c_1609, c_22])).
% 5.31/1.99  tff(c_1778, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_34, c_1767])).
% 5.31/1.99  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.31/1.99  tff(c_1639, plain, (![A_334]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_334, '#skF_6'))), inference(resolution, [status(thm)], [c_40, c_1628])).
% 5.31/1.99  tff(c_1653, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_1639])).
% 5.31/1.99  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.31/1.99  tff(c_1640, plain, (![A_334]: (~v1_xboole_0('#skF_2') | ~r2_hidden(A_334, '#skF_5'))), inference(resolution, [status(thm)], [c_42, c_1628])).
% 5.31/1.99  tff(c_1652, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_1640])).
% 5.31/1.99  tff(c_36, plain, (m1_subset_1('#skF_8', k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.31/1.99  tff(c_1674, plain, (![A_342, B_343, C_344, D_345]: (k7_mcart_1(A_342, B_343, C_344, D_345)=k2_mcart_1(D_345) | ~m1_subset_1(D_345, k3_zfmisc_1(A_342, B_343, C_344)) | k1_xboole_0=C_344 | k1_xboole_0=B_343 | k1_xboole_0=A_342)), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.31/1.99  tff(c_1678, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_1674])).
% 5.31/1.99  tff(c_1800, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1678])).
% 5.31/1.99  tff(c_1585, plain, (![A_320, B_321]: (r2_hidden('#skF_1'(A_320, B_321), A_320) | r1_tarski(A_320, B_321))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.31/1.99  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.31/1.99  tff(c_1591, plain, (![A_322]: (r1_tarski(A_322, A_322))), inference(resolution, [status(thm)], [c_1585, c_4])).
% 5.31/1.99  tff(c_10, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.31/1.99  tff(c_1575, plain, (![B_317, A_318]: (~r1_xboole_0(B_317, A_318) | ~r1_tarski(B_317, A_318) | v1_xboole_0(B_317))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.31/1.99  tff(c_1583, plain, (![A_8]: (~r1_tarski(A_8, k1_xboole_0) | v1_xboole_0(A_8))), inference(resolution, [status(thm)], [c_10, c_1575])).
% 5.31/1.99  tff(c_1596, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_1591, c_1583])).
% 5.31/1.99  tff(c_1803, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1800, c_1596])).
% 5.31/1.99  tff(c_1808, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1652, c_1803])).
% 5.31/1.99  tff(c_1810, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_1678])).
% 5.31/1.99  tff(c_1762, plain, (![A_356, B_357, C_358, D_359]: (k6_mcart_1(A_356, B_357, C_358, D_359)=k2_mcart_1(k1_mcart_1(D_359)) | ~m1_subset_1(D_359, k3_zfmisc_1(A_356, B_357, C_358)) | k1_xboole_0=C_358 | k1_xboole_0=B_357 | k1_xboole_0=A_356)), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.31/1.99  tff(c_1766, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_1762])).
% 5.31/1.99  tff(c_1869, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1810, c_1766])).
% 5.31/1.99  tff(c_1870, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1869])).
% 5.31/1.99  tff(c_1875, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1870, c_1596])).
% 5.31/1.99  tff(c_1880, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1653, c_1875])).
% 5.31/1.99  tff(c_1882, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_1869])).
% 5.31/1.99  tff(c_1809, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4' | k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitRight, [status(thm)], [c_1678])).
% 5.31/1.99  tff(c_2009, plain, (k1_xboole_0='#skF_4' | k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_1882, c_1809])).
% 5.31/1.99  tff(c_2010, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitLeft, [status(thm)], [c_2009])).
% 5.31/1.99  tff(c_131, plain, (![C_63, B_64, A_65]: (~v1_xboole_0(C_63) | ~m1_subset_1(B_64, k1_zfmisc_1(C_63)) | ~r2_hidden(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.31/1.99  tff(c_141, plain, (![A_65]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_65, '#skF_7'))), inference(resolution, [status(thm)], [c_38, c_131])).
% 5.31/1.99  tff(c_144, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_141])).
% 5.31/1.99  tff(c_32, plain, (~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7') | ~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6') | ~r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.31/1.99  tff(c_66, plain, (~r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(splitLeft, [status(thm)], [c_32])).
% 5.31/1.99  tff(c_142, plain, (![A_65]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_65, '#skF_6'))), inference(resolution, [status(thm)], [c_40, c_131])).
% 5.31/1.99  tff(c_145, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_142])).
% 5.31/1.99  tff(c_143, plain, (![A_65]: (~v1_xboole_0('#skF_2') | ~r2_hidden(A_65, '#skF_5'))), inference(resolution, [status(thm)], [c_42, c_131])).
% 5.31/1.99  tff(c_146, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_143])).
% 5.31/1.99  tff(c_228, plain, (![A_89, B_90, C_91, D_92]: (k7_mcart_1(A_89, B_90, C_91, D_92)=k2_mcart_1(D_92) | ~m1_subset_1(D_92, k3_zfmisc_1(A_89, B_90, C_91)) | k1_xboole_0=C_91 | k1_xboole_0=B_90 | k1_xboole_0=A_89)), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.31/1.99  tff(c_232, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_228])).
% 5.31/1.99  tff(c_254, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_232])).
% 5.31/1.99  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.31/1.99  tff(c_85, plain, (![A_52, B_53]: (~r2_hidden('#skF_1'(A_52, B_53), B_53) | r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.31/1.99  tff(c_91, plain, (![A_54]: (r1_tarski(A_54, A_54))), inference(resolution, [status(thm)], [c_6, c_85])).
% 5.31/1.99  tff(c_44, plain, (![B_39, A_40]: (r1_xboole_0(B_39, A_40) | ~r1_xboole_0(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.31/1.99  tff(c_47, plain, (![A_8]: (r1_xboole_0(k1_xboole_0, A_8))), inference(resolution, [status(thm)], [c_10, c_44])).
% 5.31/1.99  tff(c_72, plain, (![B_46, A_47]: (~r1_xboole_0(B_46, A_47) | ~r1_tarski(B_46, A_47) | v1_xboole_0(B_46))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.31/1.99  tff(c_79, plain, (![A_8]: (~r1_tarski(k1_xboole_0, A_8) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_47, c_72])).
% 5.31/1.99  tff(c_82, plain, (![A_8]: (~r1_tarski(k1_xboole_0, A_8))), inference(splitLeft, [status(thm)], [c_79])).
% 5.31/1.99  tff(c_100, plain, $false, inference(resolution, [status(thm)], [c_91, c_82])).
% 5.31/1.99  tff(c_101, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_79])).
% 5.31/1.99  tff(c_256, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_254, c_101])).
% 5.31/1.99  tff(c_261, plain, $false, inference(negUnitSimplification, [status(thm)], [c_146, c_256])).
% 5.31/1.99  tff(c_263, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_232])).
% 5.31/1.99  tff(c_379, plain, (![A_107, B_108, C_109, D_110]: (k5_mcart_1(A_107, B_108, C_109, D_110)=k1_mcart_1(k1_mcart_1(D_110)) | ~m1_subset_1(D_110, k3_zfmisc_1(A_107, B_108, C_109)) | k1_xboole_0=C_109 | k1_xboole_0=B_108 | k1_xboole_0=A_107)), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.31/1.99  tff(c_382, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_379])).
% 5.31/1.99  tff(c_385, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_263, c_382])).
% 5.31/1.99  tff(c_495, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_385])).
% 5.31/1.99  tff(c_500, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_495, c_101])).
% 5.31/1.99  tff(c_505, plain, $false, inference(negUnitSimplification, [status(thm)], [c_145, c_500])).
% 5.31/1.99  tff(c_506, plain, (k1_xboole_0='#skF_4' | k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_385])).
% 5.31/1.99  tff(c_508, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitLeft, [status(thm)], [c_506])).
% 5.31/1.99  tff(c_20, plain, (![A_16, B_17, C_18]: (k2_zfmisc_1(k2_zfmisc_1(A_16, B_17), C_18)=k3_zfmisc_1(A_16, B_17, C_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.31/1.99  tff(c_201, plain, (![A_81, B_82, C_83]: (r2_hidden(k1_mcart_1(A_81), B_82) | ~r2_hidden(A_81, k2_zfmisc_1(B_82, C_83)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.31/1.99  tff(c_518, plain, (![A_131, A_132, B_133, C_134]: (r2_hidden(k1_mcart_1(A_131), k2_zfmisc_1(A_132, B_133)) | ~r2_hidden(A_131, k3_zfmisc_1(A_132, B_133, C_134)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_201])).
% 5.31/1.99  tff(c_537, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_34, c_518])).
% 5.31/1.99  tff(c_24, plain, (![A_19, B_20, C_21]: (r2_hidden(k1_mcart_1(A_19), B_20) | ~r2_hidden(A_19, k2_zfmisc_1(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.31/1.99  tff(c_539, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')), '#skF_5')), inference(resolution, [status(thm)], [c_537, c_24])).
% 5.31/1.99  tff(c_547, plain, (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_508, c_539])).
% 5.31/1.99  tff(c_549, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_547])).
% 5.31/1.99  tff(c_550, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_506])).
% 5.31/1.99  tff(c_557, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_550, c_101])).
% 5.31/1.99  tff(c_562, plain, $false, inference(negUnitSimplification, [status(thm)], [c_144, c_557])).
% 5.31/1.99  tff(c_563, plain, (![A_65]: (~r2_hidden(A_65, '#skF_5'))), inference(splitRight, [status(thm)], [c_143])).
% 5.31/1.99  tff(c_608, plain, (![A_145, B_146, C_147]: (r2_hidden(k1_mcart_1(A_145), B_146) | ~r2_hidden(A_145, k2_zfmisc_1(B_146, C_147)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.31/1.99  tff(c_998, plain, (![A_210, A_211, B_212, C_213]: (r2_hidden(k1_mcart_1(A_210), k2_zfmisc_1(A_211, B_212)) | ~r2_hidden(A_210, k3_zfmisc_1(A_211, B_212, C_213)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_608])).
% 5.31/1.99  tff(c_1017, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_34, c_998])).
% 5.31/1.99  tff(c_1023, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')), '#skF_5')), inference(resolution, [status(thm)], [c_1017, c_24])).
% 5.31/1.99  tff(c_1031, plain, $false, inference(negUnitSimplification, [status(thm)], [c_563, c_1023])).
% 5.31/1.99  tff(c_1032, plain, (![A_65]: (~r2_hidden(A_65, '#skF_6'))), inference(splitRight, [status(thm)], [c_142])).
% 5.31/1.99  tff(c_1085, plain, (![A_227, B_228, C_229]: (r2_hidden(k1_mcart_1(A_227), B_228) | ~r2_hidden(A_227, k2_zfmisc_1(B_228, C_229)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.31/1.99  tff(c_1425, plain, (![A_280, A_281, B_282, C_283]: (r2_hidden(k1_mcart_1(A_280), k2_zfmisc_1(A_281, B_282)) | ~r2_hidden(A_280, k3_zfmisc_1(A_281, B_282, C_283)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1085])).
% 5.31/1.99  tff(c_1444, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_34, c_1425])).
% 5.31/1.99  tff(c_1452, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_6')), inference(resolution, [status(thm)], [c_1444, c_22])).
% 5.31/1.99  tff(c_1459, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1032, c_1452])).
% 5.31/1.99  tff(c_1460, plain, (![A_65]: (~r2_hidden(A_65, '#skF_7'))), inference(splitRight, [status(thm)], [c_141])).
% 5.31/1.99  tff(c_1532, plain, (![A_301, C_302, B_303]: (r2_hidden(k2_mcart_1(A_301), C_302) | ~r2_hidden(A_301, k2_zfmisc_1(B_303, C_302)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.31/1.99  tff(c_1556, plain, (![A_309, C_310, A_311, B_312]: (r2_hidden(k2_mcart_1(A_309), C_310) | ~r2_hidden(A_309, k3_zfmisc_1(A_311, B_312, C_310)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1532])).
% 5.31/1.99  tff(c_1561, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_34, c_1556])).
% 5.31/1.99  tff(c_1566, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1460, c_1561])).
% 5.31/1.99  tff(c_1567, plain, (~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6') | ~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_32])).
% 5.31/1.99  tff(c_1598, plain, (~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_1567])).
% 5.31/1.99  tff(c_2011, plain, (~r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2010, c_1598])).
% 5.31/1.99  tff(c_2014, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1778, c_2011])).
% 5.31/1.99  tff(c_2015, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_2009])).
% 5.31/1.99  tff(c_2022, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2015, c_1596])).
% 5.31/1.99  tff(c_2027, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1651, c_2022])).
% 5.31/1.99  tff(c_2028, plain, (![A_334]: (~r2_hidden(A_334, '#skF_6'))), inference(splitRight, [status(thm)], [c_1639])).
% 5.31/1.99  tff(c_2565, plain, (![A_465, A_466, B_467, C_468]: (r2_hidden(k1_mcart_1(A_465), k2_zfmisc_1(A_466, B_467)) | ~r2_hidden(A_465, k3_zfmisc_1(A_466, B_467, C_468)))), inference(superposition, [status(thm), theory('equality')], [c_1609, c_24])).
% 5.31/1.99  tff(c_2591, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_34, c_2565])).
% 5.31/1.99  tff(c_2599, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_6')), inference(resolution, [status(thm)], [c_2591, c_22])).
% 5.31/1.99  tff(c_2606, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2028, c_2599])).
% 5.31/1.99  tff(c_2607, plain, (![A_334]: (~r2_hidden(A_334, '#skF_5'))), inference(splitRight, [status(thm)], [c_1640])).
% 5.31/1.99  tff(c_1568, plain, (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(splitRight, [status(thm)], [c_32])).
% 5.31/1.99  tff(c_2610, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2607, c_1568])).
% 5.31/1.99  tff(c_2611, plain, (![A_334]: (~r2_hidden(A_334, '#skF_7'))), inference(splitRight, [status(thm)], [c_1638])).
% 5.31/1.99  tff(c_2709, plain, (![A_490, C_491, A_492, B_493]: (r2_hidden(k2_mcart_1(A_490), C_491) | ~r2_hidden(A_490, k3_zfmisc_1(A_492, B_493, C_491)))), inference(superposition, [status(thm), theory('equality')], [c_1609, c_22])).
% 5.31/1.99  tff(c_2714, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_34, c_2709])).
% 5.31/1.99  tff(c_2719, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2611, c_2714])).
% 5.31/1.99  tff(c_2720, plain, (~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6')), inference(splitRight, [status(thm)], [c_1567])).
% 5.31/1.99  tff(c_2722, plain, (![C_494, B_495, A_496]: (~v1_xboole_0(C_494) | ~m1_subset_1(B_495, k1_zfmisc_1(C_494)) | ~r2_hidden(A_496, B_495))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.31/1.99  tff(c_2732, plain, (![A_496]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_496, '#skF_7'))), inference(resolution, [status(thm)], [c_38, c_2722])).
% 5.31/1.99  tff(c_2735, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_2732])).
% 5.31/1.99  tff(c_2733, plain, (![A_496]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_496, '#skF_6'))), inference(resolution, [status(thm)], [c_40, c_2722])).
% 5.31/1.99  tff(c_2736, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_2733])).
% 5.31/1.99  tff(c_2734, plain, (![A_496]: (~v1_xboole_0('#skF_2') | ~r2_hidden(A_496, '#skF_5'))), inference(resolution, [status(thm)], [c_42, c_2722])).
% 5.31/1.99  tff(c_2752, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_2734])).
% 5.31/1.99  tff(c_2919, plain, (![A_528, B_529, C_530, D_531]: (k7_mcart_1(A_528, B_529, C_530, D_531)=k2_mcart_1(D_531) | ~m1_subset_1(D_531, k3_zfmisc_1(A_528, B_529, C_530)) | k1_xboole_0=C_530 | k1_xboole_0=B_529 | k1_xboole_0=A_528)), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.31/1.99  tff(c_2923, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_2919])).
% 5.31/1.99  tff(c_2980, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_2923])).
% 5.31/1.99  tff(c_2982, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2980, c_1596])).
% 5.31/1.99  tff(c_2987, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2752, c_2982])).
% 5.31/1.99  tff(c_2989, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_2923])).
% 5.31/1.99  tff(c_3025, plain, (![A_539, B_540, C_541, D_542]: (k5_mcart_1(A_539, B_540, C_541, D_542)=k1_mcart_1(k1_mcart_1(D_542)) | ~m1_subset_1(D_542, k3_zfmisc_1(A_539, B_540, C_541)) | k1_xboole_0=C_541 | k1_xboole_0=B_540 | k1_xboole_0=A_539)), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.31/1.99  tff(c_3028, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_3025])).
% 5.31/1.99  tff(c_3031, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_2989, c_3028])).
% 5.31/1.99  tff(c_3218, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_3031])).
% 5.31/1.99  tff(c_3223, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3218, c_1596])).
% 5.31/1.99  tff(c_3228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2736, c_3223])).
% 5.31/1.99  tff(c_3230, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_3031])).
% 5.31/1.99  tff(c_3092, plain, (![A_548, B_549, C_550, D_551]: (k6_mcart_1(A_548, B_549, C_550, D_551)=k2_mcart_1(k1_mcart_1(D_551)) | ~m1_subset_1(D_551, k3_zfmisc_1(A_548, B_549, C_550)) | k1_xboole_0=C_550 | k1_xboole_0=B_549 | k1_xboole_0=A_548)), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.31/1.99  tff(c_3095, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_3092])).
% 5.31/1.99  tff(c_3098, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_2989, c_3095])).
% 5.31/1.99  tff(c_3316, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_3230, c_3098])).
% 5.31/1.99  tff(c_3317, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_3316])).
% 5.31/1.99  tff(c_3323, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3317, c_1596])).
% 5.31/1.99  tff(c_3328, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2735, c_3323])).
% 5.31/1.99  tff(c_3329, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_3316])).
% 5.31/1.99  tff(c_2792, plain, (![A_506, B_507, C_508]: (r2_hidden(k1_mcart_1(A_506), B_507) | ~r2_hidden(A_506, k2_zfmisc_1(B_507, C_508)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.31/1.99  tff(c_3244, plain, (![A_577, A_578, B_579, C_580]: (r2_hidden(k1_mcart_1(A_577), k2_zfmisc_1(A_578, B_579)) | ~r2_hidden(A_577, k3_zfmisc_1(A_578, B_579, C_580)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_2792])).
% 5.31/1.99  tff(c_3270, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_34, c_3244])).
% 5.31/1.99  tff(c_3279, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_6')), inference(resolution, [status(thm)], [c_3270, c_22])).
% 5.31/1.99  tff(c_3356, plain, (r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3329, c_3279])).
% 5.31/1.99  tff(c_3358, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2720, c_3356])).
% 5.31/1.99  tff(c_3359, plain, (![A_496]: (~r2_hidden(A_496, '#skF_5'))), inference(splitRight, [status(thm)], [c_2734])).
% 5.31/1.99  tff(c_3362, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3359, c_1568])).
% 5.31/1.99  tff(c_3363, plain, (![A_496]: (~r2_hidden(A_496, '#skF_6'))), inference(splitRight, [status(thm)], [c_2733])).
% 5.31/1.99  tff(c_3478, plain, (![A_603, B_604, C_605]: (r2_hidden(k1_mcart_1(A_603), B_604) | ~r2_hidden(A_603, k2_zfmisc_1(B_604, C_605)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.31/1.99  tff(c_3899, plain, (![A_657, A_658, B_659, C_660]: (r2_hidden(k1_mcart_1(A_657), k2_zfmisc_1(A_658, B_659)) | ~r2_hidden(A_657, k3_zfmisc_1(A_658, B_659, C_660)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_3478])).
% 5.31/1.99  tff(c_3926, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_34, c_3899])).
% 5.31/1.99  tff(c_3932, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_6')), inference(resolution, [status(thm)], [c_3926, c_22])).
% 5.31/1.99  tff(c_3940, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3363, c_3932])).
% 5.31/1.99  tff(c_3941, plain, (![A_496]: (~r2_hidden(A_496, '#skF_7'))), inference(splitRight, [status(thm)], [c_2732])).
% 5.31/1.99  tff(c_2721, plain, (r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_1567])).
% 5.31/1.99  tff(c_3944, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3941, c_2721])).
% 5.31/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.31/1.99  
% 5.31/1.99  Inference rules
% 5.31/1.99  ----------------------
% 5.31/1.99  #Ref     : 0
% 5.31/1.99  #Sup     : 914
% 5.31/1.99  #Fact    : 0
% 5.31/1.99  #Define  : 0
% 5.31/1.99  #Split   : 57
% 5.31/1.99  #Chain   : 0
% 5.31/1.99  #Close   : 0
% 5.31/1.99  
% 5.31/1.99  Ordering : KBO
% 5.31/1.99  
% 5.31/1.99  Simplification rules
% 5.31/1.99  ----------------------
% 5.31/1.99  #Subsume      : 330
% 5.31/1.99  #Demod        : 275
% 5.31/1.99  #Tautology    : 121
% 5.31/1.99  #SimpNegUnit  : 37
% 5.31/1.99  #BackRed      : 111
% 5.31/1.99  
% 5.31/1.99  #Partial instantiations: 0
% 5.31/1.99  #Strategies tried      : 1
% 5.31/1.99  
% 5.31/1.99  Timing (in seconds)
% 5.31/1.99  ----------------------
% 5.31/1.99  Preprocessing        : 0.34
% 5.31/1.99  Parsing              : 0.18
% 5.31/1.99  CNF conversion       : 0.03
% 5.31/1.99  Main loop            : 0.84
% 5.31/1.99  Inferencing          : 0.31
% 5.31/1.99  Reduction            : 0.26
% 5.31/1.99  Demodulation         : 0.17
% 5.31/1.99  BG Simplification    : 0.03
% 5.31/1.99  Subsumption          : 0.16
% 5.31/1.99  Abstraction          : 0.04
% 5.31/1.99  MUC search           : 0.00
% 5.31/1.99  Cooper               : 0.00
% 5.31/1.99  Total                : 1.24
% 5.31/1.99  Index Insertion      : 0.00
% 5.31/1.99  Index Deletion       : 0.00
% 5.31/1.99  Index Matching       : 0.00
% 5.31/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
