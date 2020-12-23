%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:00 EST 2020

% Result     : Theorem 5.29s
% Output     : CNFRefutation 5.61s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 337 expanded)
%              Number of leaves         :   33 ( 123 expanded)
%              Depth                    :   11
%              Number of atoms          :  145 ( 708 expanded)
%              Number of equality atoms :   56 ( 226 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_118,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_73,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ~ ( B != k1_xboole_0
          & ! [C] :
              ( m1_subset_1(C,A)
             => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_101,plain,(
    ! [A_55,B_56] :
      ( ~ r2_hidden('#skF_1'(A_55,B_56),B_56)
      | r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_110,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_101])).

tff(c_52,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_26,plain,(
    ! [A_15,B_16] :
      ( r2_hidden('#skF_4'(A_15,B_16),B_16)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_130,plain,(
    ! [C_62,B_63,A_64] :
      ( r2_hidden(C_62,B_63)
      | ~ r2_hidden(C_62,A_64)
      | ~ r1_tarski(A_64,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_688,plain,(
    ! [A_149,B_150,B_151] :
      ( r2_hidden('#skF_4'(A_149,B_150),B_151)
      | ~ r1_tarski(B_150,B_151)
      | ~ r2_hidden(A_149,B_150) ) ),
    inference(resolution,[status(thm)],[c_26,c_130])).

tff(c_119,plain,(
    ! [A_60,B_61] :
      ( k2_xboole_0(k1_tarski(A_60),B_61) = B_61
      | ~ r2_hidden(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [A_13,B_14] : k2_xboole_0(k1_tarski(A_13),B_14) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_124,plain,(
    ! [B_61,A_60] :
      ( k1_xboole_0 != B_61
      | ~ r2_hidden(A_60,B_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_22])).

tff(c_734,plain,(
    ! [B_152,B_153,A_154] :
      ( k1_xboole_0 != B_152
      | ~ r1_tarski(B_153,B_152)
      | ~ r2_hidden(A_154,B_153) ) ),
    inference(resolution,[status(thm)],[c_688,c_124])).

tff(c_791,plain,(
    ! [A_154] :
      ( k1_xboole_0 != '#skF_8'
      | ~ r2_hidden(A_154,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_52,c_734])).

tff(c_792,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_791])).

tff(c_54,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k1_zfmisc_1('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_184,plain,(
    ! [A_74,B_75] :
      ( k6_setfam_1(A_74,B_75) = k1_setfam_1(B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(k1_zfmisc_1(A_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_201,plain,(
    k6_setfam_1('#skF_6','#skF_8') = k1_setfam_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_54,c_184])).

tff(c_1494,plain,(
    ! [A_212,B_213] :
      ( k8_setfam_1(A_212,B_213) = k6_setfam_1(A_212,B_213)
      | k1_xboole_0 = B_213
      | ~ m1_subset_1(B_213,k1_zfmisc_1(k1_zfmisc_1(A_212))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1540,plain,
    ( k8_setfam_1('#skF_6','#skF_8') = k6_setfam_1('#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_54,c_1494])).

tff(c_1560,plain,
    ( k8_setfam_1('#skF_6','#skF_8') = k1_setfam_1('#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_1540])).

tff(c_1561,plain,(
    k8_setfam_1('#skF_6','#skF_8') = k1_setfam_1('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_792,c_1560])).

tff(c_359,plain,(
    ! [A_94,B_95] :
      ( m1_subset_1(k8_setfam_1(A_94,B_95),k1_zfmisc_1(A_94))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(k1_zfmisc_1(A_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_42,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(A_32,B_33)
      | ~ m1_subset_1(A_32,k1_zfmisc_1(B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_532,plain,(
    ! [A_128,B_129] :
      ( r1_tarski(k8_setfam_1(A_128,B_129),A_128)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(k1_zfmisc_1(A_128))) ) ),
    inference(resolution,[status(thm)],[c_359,c_42])).

tff(c_565,plain,(
    r1_tarski(k8_setfam_1('#skF_6','#skF_8'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_532])).

tff(c_1565,plain,(
    r1_tarski(k1_setfam_1('#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1561,c_565])).

tff(c_56,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_200,plain,(
    k6_setfam_1('#skF_6','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_184])).

tff(c_1537,plain,
    ( k8_setfam_1('#skF_6','#skF_7') = k6_setfam_1('#skF_6','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_56,c_1494])).

tff(c_1558,plain,
    ( k8_setfam_1('#skF_6','#skF_7') = k1_setfam_1('#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_1537])).

tff(c_1601,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_1558])).

tff(c_32,plain,(
    ! [A_25] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_34,plain,(
    ! [A_26] :
      ( k8_setfam_1(A_26,k1_xboole_0) = A_26
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_58,plain,(
    ! [A_26] : k8_setfam_1(A_26,k1_xboole_0) = A_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34])).

tff(c_1636,plain,(
    ! [A_26] : k8_setfam_1(A_26,'#skF_7') = A_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1601,c_58])).

tff(c_50,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_6','#skF_8'),k8_setfam_1('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1567,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_8'),k8_setfam_1('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1561,c_50])).

tff(c_1676,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1636,c_1567])).

tff(c_1680,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1565,c_1676])).

tff(c_1682,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1558])).

tff(c_48,plain,(
    ! [B_38,A_37] :
      ( r1_tarski(k1_setfam_1(B_38),k1_setfam_1(A_37))
      | k1_xboole_0 = A_37
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1681,plain,(
    k8_setfam_1('#skF_6','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_1558])).

tff(c_1683,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_8'),k1_setfam_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1681,c_1567])).

tff(c_1713,plain,
    ( k1_xboole_0 = '#skF_7'
    | ~ r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_1683])).

tff(c_1719,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1713])).

tff(c_1721,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1682,c_1719])).

tff(c_1723,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_791])).

tff(c_1740,plain,(
    ! [A_26] : k8_setfam_1(A_26,'#skF_8') = A_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1723,c_58])).

tff(c_36,plain,(
    ! [A_26,B_27] :
      ( k8_setfam_1(A_26,B_27) = k6_setfam_1(A_26,B_27)
      | k1_xboole_0 = B_27
      | ~ m1_subset_1(B_27,k1_zfmisc_1(k1_zfmisc_1(A_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1794,plain,(
    ! [A_227,B_228] :
      ( k8_setfam_1(A_227,B_228) = k6_setfam_1(A_227,B_228)
      | B_228 = '#skF_8'
      | ~ m1_subset_1(B_228,k1_zfmisc_1(k1_zfmisc_1(A_227))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1723,c_36])).

tff(c_1817,plain,
    ( k8_setfam_1('#skF_6','#skF_7') = k6_setfam_1('#skF_6','#skF_7')
    | '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_56,c_1794])).

tff(c_1829,plain,
    ( k8_setfam_1('#skF_6','#skF_7') = k1_setfam_1('#skF_7')
    | '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_1817])).

tff(c_2094,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1829])).

tff(c_1774,plain,(
    ~ r1_tarski('#skF_6',k8_setfam_1('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1740,c_50])).

tff(c_2099,plain,(
    ~ r1_tarski('#skF_6',k8_setfam_1('#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2094,c_1774])).

tff(c_2107,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_1740,c_2099])).

tff(c_2109,plain,(
    '#skF_7' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1829])).

tff(c_1746,plain,(
    ! [A_223] : ~ r2_hidden(A_223,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_791])).

tff(c_1761,plain,(
    ! [B_2] : r1_tarski('#skF_7',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_1746])).

tff(c_638,plain,(
    ! [A_147,B_148] :
      ( r2_hidden('#skF_5'(A_147,B_148),B_148)
      | k1_xboole_0 = B_148
      | ~ m1_subset_1(B_148,k1_zfmisc_1(A_147)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_684,plain,(
    ! [A_147,B_148,B_2] :
      ( r2_hidden('#skF_5'(A_147,B_148),B_2)
      | ~ r1_tarski(B_148,B_2)
      | k1_xboole_0 = B_148
      | ~ m1_subset_1(B_148,k1_zfmisc_1(A_147)) ) ),
    inference(resolution,[status(thm)],[c_638,c_2])).

tff(c_3707,plain,(
    ! [A_326,B_327,B_328] :
      ( r2_hidden('#skF_5'(A_326,B_327),B_328)
      | ~ r1_tarski(B_327,B_328)
      | B_327 = '#skF_8'
      | ~ m1_subset_1(B_327,k1_zfmisc_1(A_326)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1723,c_684])).

tff(c_1722,plain,(
    ! [A_154] : ~ r2_hidden(A_154,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_791])).

tff(c_3802,plain,(
    ! [B_329,A_330] :
      ( ~ r1_tarski(B_329,'#skF_7')
      | B_329 = '#skF_8'
      | ~ m1_subset_1(B_329,k1_zfmisc_1(A_330)) ) ),
    inference(resolution,[status(thm)],[c_3707,c_1722])).

tff(c_3835,plain,
    ( ~ r1_tarski('#skF_7','#skF_7')
    | '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_56,c_3802])).

tff(c_3850,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1761,c_3835])).

tff(c_3852,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2109,c_3850])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:34:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.29/1.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.29/1.97  
% 5.29/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.29/1.97  %$ r2_hidden > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 5.29/1.97  
% 5.29/1.97  %Foreground sorts:
% 5.29/1.97  
% 5.29/1.97  
% 5.29/1.97  %Background operators:
% 5.29/1.97  
% 5.29/1.97  
% 5.29/1.97  %Foreground operators:
% 5.29/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.29/1.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.29/1.97  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.29/1.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.29/1.97  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 5.29/1.97  tff('#skF_7', type, '#skF_7': $i).
% 5.29/1.97  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.29/1.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.29/1.97  tff('#skF_6', type, '#skF_6': $i).
% 5.29/1.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.29/1.97  tff('#skF_8', type, '#skF_8': $i).
% 5.29/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.29/1.97  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 5.29/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.29/1.97  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.29/1.97  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.29/1.97  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.29/1.97  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.29/1.97  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.29/1.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.29/1.97  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.29/1.97  
% 5.61/1.99  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.61/1.99  tff(f_118, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_setfam_1)).
% 5.61/1.99  tff(f_59, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 5.61/1.99  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 5.61/1.99  tff(f_46, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 5.61/1.99  tff(f_92, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 5.61/1.99  tff(f_84, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 5.61/1.99  tff(f_88, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 5.61/1.99  tff(f_96, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.61/1.99  tff(f_73, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 5.61/1.99  tff(f_108, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 5.61/1.99  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_subset_1)).
% 5.61/1.99  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.61/1.99  tff(c_101, plain, (![A_55, B_56]: (~r2_hidden('#skF_1'(A_55, B_56), B_56) | r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.61/1.99  tff(c_110, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_101])).
% 5.61/1.99  tff(c_52, plain, (r1_tarski('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.61/1.99  tff(c_26, plain, (![A_15, B_16]: (r2_hidden('#skF_4'(A_15, B_16), B_16) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.61/1.99  tff(c_130, plain, (![C_62, B_63, A_64]: (r2_hidden(C_62, B_63) | ~r2_hidden(C_62, A_64) | ~r1_tarski(A_64, B_63))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.61/1.99  tff(c_688, plain, (![A_149, B_150, B_151]: (r2_hidden('#skF_4'(A_149, B_150), B_151) | ~r1_tarski(B_150, B_151) | ~r2_hidden(A_149, B_150))), inference(resolution, [status(thm)], [c_26, c_130])).
% 5.61/1.99  tff(c_119, plain, (![A_60, B_61]: (k2_xboole_0(k1_tarski(A_60), B_61)=B_61 | ~r2_hidden(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.61/1.99  tff(c_22, plain, (![A_13, B_14]: (k2_xboole_0(k1_tarski(A_13), B_14)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.61/1.99  tff(c_124, plain, (![B_61, A_60]: (k1_xboole_0!=B_61 | ~r2_hidden(A_60, B_61))), inference(superposition, [status(thm), theory('equality')], [c_119, c_22])).
% 5.61/1.99  tff(c_734, plain, (![B_152, B_153, A_154]: (k1_xboole_0!=B_152 | ~r1_tarski(B_153, B_152) | ~r2_hidden(A_154, B_153))), inference(resolution, [status(thm)], [c_688, c_124])).
% 5.61/1.99  tff(c_791, plain, (![A_154]: (k1_xboole_0!='#skF_8' | ~r2_hidden(A_154, '#skF_7'))), inference(resolution, [status(thm)], [c_52, c_734])).
% 5.61/1.99  tff(c_792, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_791])).
% 5.61/1.99  tff(c_54, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_zfmisc_1('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.61/1.99  tff(c_184, plain, (![A_74, B_75]: (k6_setfam_1(A_74, B_75)=k1_setfam_1(B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(k1_zfmisc_1(A_74))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.61/1.99  tff(c_201, plain, (k6_setfam_1('#skF_6', '#skF_8')=k1_setfam_1('#skF_8')), inference(resolution, [status(thm)], [c_54, c_184])).
% 5.61/1.99  tff(c_1494, plain, (![A_212, B_213]: (k8_setfam_1(A_212, B_213)=k6_setfam_1(A_212, B_213) | k1_xboole_0=B_213 | ~m1_subset_1(B_213, k1_zfmisc_1(k1_zfmisc_1(A_212))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.61/1.99  tff(c_1540, plain, (k8_setfam_1('#skF_6', '#skF_8')=k6_setfam_1('#skF_6', '#skF_8') | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_54, c_1494])).
% 5.61/1.99  tff(c_1560, plain, (k8_setfam_1('#skF_6', '#skF_8')=k1_setfam_1('#skF_8') | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_201, c_1540])).
% 5.61/1.99  tff(c_1561, plain, (k8_setfam_1('#skF_6', '#skF_8')=k1_setfam_1('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_792, c_1560])).
% 5.61/1.99  tff(c_359, plain, (![A_94, B_95]: (m1_subset_1(k8_setfam_1(A_94, B_95), k1_zfmisc_1(A_94)) | ~m1_subset_1(B_95, k1_zfmisc_1(k1_zfmisc_1(A_94))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.61/1.99  tff(c_42, plain, (![A_32, B_33]: (r1_tarski(A_32, B_33) | ~m1_subset_1(A_32, k1_zfmisc_1(B_33)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.61/1.99  tff(c_532, plain, (![A_128, B_129]: (r1_tarski(k8_setfam_1(A_128, B_129), A_128) | ~m1_subset_1(B_129, k1_zfmisc_1(k1_zfmisc_1(A_128))))), inference(resolution, [status(thm)], [c_359, c_42])).
% 5.61/1.99  tff(c_565, plain, (r1_tarski(k8_setfam_1('#skF_6', '#skF_8'), '#skF_6')), inference(resolution, [status(thm)], [c_54, c_532])).
% 5.61/1.99  tff(c_1565, plain, (r1_tarski(k1_setfam_1('#skF_8'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1561, c_565])).
% 5.61/1.99  tff(c_56, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.61/1.99  tff(c_200, plain, (k6_setfam_1('#skF_6', '#skF_7')=k1_setfam_1('#skF_7')), inference(resolution, [status(thm)], [c_56, c_184])).
% 5.61/1.99  tff(c_1537, plain, (k8_setfam_1('#skF_6', '#skF_7')=k6_setfam_1('#skF_6', '#skF_7') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_56, c_1494])).
% 5.61/1.99  tff(c_1558, plain, (k8_setfam_1('#skF_6', '#skF_7')=k1_setfam_1('#skF_7') | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_200, c_1537])).
% 5.61/1.99  tff(c_1601, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_1558])).
% 5.61/1.99  tff(c_32, plain, (![A_25]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.61/1.99  tff(c_34, plain, (![A_26]: (k8_setfam_1(A_26, k1_xboole_0)=A_26 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_26))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.61/1.99  tff(c_58, plain, (![A_26]: (k8_setfam_1(A_26, k1_xboole_0)=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34])).
% 5.61/1.99  tff(c_1636, plain, (![A_26]: (k8_setfam_1(A_26, '#skF_7')=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_1601, c_58])).
% 5.61/1.99  tff(c_50, plain, (~r1_tarski(k8_setfam_1('#skF_6', '#skF_8'), k8_setfam_1('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.61/1.99  tff(c_1567, plain, (~r1_tarski(k1_setfam_1('#skF_8'), k8_setfam_1('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1561, c_50])).
% 5.61/1.99  tff(c_1676, plain, (~r1_tarski(k1_setfam_1('#skF_8'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1636, c_1567])).
% 5.61/1.99  tff(c_1680, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1565, c_1676])).
% 5.61/1.99  tff(c_1682, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_1558])).
% 5.61/1.99  tff(c_48, plain, (![B_38, A_37]: (r1_tarski(k1_setfam_1(B_38), k1_setfam_1(A_37)) | k1_xboole_0=A_37 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.61/1.99  tff(c_1681, plain, (k8_setfam_1('#skF_6', '#skF_7')=k1_setfam_1('#skF_7')), inference(splitRight, [status(thm)], [c_1558])).
% 5.61/1.99  tff(c_1683, plain, (~r1_tarski(k1_setfam_1('#skF_8'), k1_setfam_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1681, c_1567])).
% 5.61/1.99  tff(c_1713, plain, (k1_xboole_0='#skF_7' | ~r1_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_48, c_1683])).
% 5.61/1.99  tff(c_1719, plain, (k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1713])).
% 5.61/1.99  tff(c_1721, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1682, c_1719])).
% 5.61/1.99  tff(c_1723, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_791])).
% 5.61/1.99  tff(c_1740, plain, (![A_26]: (k8_setfam_1(A_26, '#skF_8')=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_1723, c_58])).
% 5.61/1.99  tff(c_36, plain, (![A_26, B_27]: (k8_setfam_1(A_26, B_27)=k6_setfam_1(A_26, B_27) | k1_xboole_0=B_27 | ~m1_subset_1(B_27, k1_zfmisc_1(k1_zfmisc_1(A_26))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.61/1.99  tff(c_1794, plain, (![A_227, B_228]: (k8_setfam_1(A_227, B_228)=k6_setfam_1(A_227, B_228) | B_228='#skF_8' | ~m1_subset_1(B_228, k1_zfmisc_1(k1_zfmisc_1(A_227))))), inference(demodulation, [status(thm), theory('equality')], [c_1723, c_36])).
% 5.61/1.99  tff(c_1817, plain, (k8_setfam_1('#skF_6', '#skF_7')=k6_setfam_1('#skF_6', '#skF_7') | '#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_56, c_1794])).
% 5.61/1.99  tff(c_1829, plain, (k8_setfam_1('#skF_6', '#skF_7')=k1_setfam_1('#skF_7') | '#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_200, c_1817])).
% 5.61/1.99  tff(c_2094, plain, ('#skF_7'='#skF_8'), inference(splitLeft, [status(thm)], [c_1829])).
% 5.61/1.99  tff(c_1774, plain, (~r1_tarski('#skF_6', k8_setfam_1('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1740, c_50])).
% 5.61/1.99  tff(c_2099, plain, (~r1_tarski('#skF_6', k8_setfam_1('#skF_6', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2094, c_1774])).
% 5.61/1.99  tff(c_2107, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_1740, c_2099])).
% 5.61/1.99  tff(c_2109, plain, ('#skF_7'!='#skF_8'), inference(splitRight, [status(thm)], [c_1829])).
% 5.61/1.99  tff(c_1746, plain, (![A_223]: (~r2_hidden(A_223, '#skF_7'))), inference(splitRight, [status(thm)], [c_791])).
% 5.61/1.99  tff(c_1761, plain, (![B_2]: (r1_tarski('#skF_7', B_2))), inference(resolution, [status(thm)], [c_6, c_1746])).
% 5.61/1.99  tff(c_638, plain, (![A_147, B_148]: (r2_hidden('#skF_5'(A_147, B_148), B_148) | k1_xboole_0=B_148 | ~m1_subset_1(B_148, k1_zfmisc_1(A_147)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.61/1.99  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.61/1.99  tff(c_684, plain, (![A_147, B_148, B_2]: (r2_hidden('#skF_5'(A_147, B_148), B_2) | ~r1_tarski(B_148, B_2) | k1_xboole_0=B_148 | ~m1_subset_1(B_148, k1_zfmisc_1(A_147)))), inference(resolution, [status(thm)], [c_638, c_2])).
% 5.61/1.99  tff(c_3707, plain, (![A_326, B_327, B_328]: (r2_hidden('#skF_5'(A_326, B_327), B_328) | ~r1_tarski(B_327, B_328) | B_327='#skF_8' | ~m1_subset_1(B_327, k1_zfmisc_1(A_326)))), inference(demodulation, [status(thm), theory('equality')], [c_1723, c_684])).
% 5.61/1.99  tff(c_1722, plain, (![A_154]: (~r2_hidden(A_154, '#skF_7'))), inference(splitRight, [status(thm)], [c_791])).
% 5.61/1.99  tff(c_3802, plain, (![B_329, A_330]: (~r1_tarski(B_329, '#skF_7') | B_329='#skF_8' | ~m1_subset_1(B_329, k1_zfmisc_1(A_330)))), inference(resolution, [status(thm)], [c_3707, c_1722])).
% 5.61/1.99  tff(c_3835, plain, (~r1_tarski('#skF_7', '#skF_7') | '#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_56, c_3802])).
% 5.61/1.99  tff(c_3850, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1761, c_3835])).
% 5.61/1.99  tff(c_3852, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2109, c_3850])).
% 5.61/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.61/1.99  
% 5.61/1.99  Inference rules
% 5.61/1.99  ----------------------
% 5.61/1.99  #Ref     : 0
% 5.61/1.99  #Sup     : 835
% 5.61/1.99  #Fact    : 0
% 5.61/1.99  #Define  : 0
% 5.61/1.99  #Split   : 8
% 5.61/1.99  #Chain   : 0
% 5.61/1.99  #Close   : 0
% 5.61/1.99  
% 5.61/1.99  Ordering : KBO
% 5.61/1.99  
% 5.61/1.99  Simplification rules
% 5.61/1.99  ----------------------
% 5.61/1.99  #Subsume      : 201
% 5.61/1.99  #Demod        : 238
% 5.61/1.99  #Tautology    : 138
% 5.61/1.99  #SimpNegUnit  : 18
% 5.61/1.99  #BackRed      : 79
% 5.61/1.99  
% 5.61/1.99  #Partial instantiations: 0
% 5.61/1.99  #Strategies tried      : 1
% 5.61/1.99  
% 5.61/1.99  Timing (in seconds)
% 5.61/1.99  ----------------------
% 5.61/1.99  Preprocessing        : 0.35
% 5.61/1.99  Parsing              : 0.18
% 5.61/1.99  CNF conversion       : 0.03
% 5.61/1.99  Main loop            : 0.87
% 5.61/1.99  Inferencing          : 0.30
% 5.61/2.00  Reduction            : 0.26
% 5.61/2.00  Demodulation         : 0.17
% 5.61/2.00  BG Simplification    : 0.04
% 5.61/2.00  Subsumption          : 0.19
% 5.61/2.00  Abstraction          : 0.05
% 5.61/2.00  MUC search           : 0.00
% 5.61/2.00  Cooper               : 0.00
% 5.61/2.00  Total                : 1.25
% 5.61/2.00  Index Insertion      : 0.00
% 5.61/2.00  Index Deletion       : 0.00
% 5.61/2.00  Index Matching       : 0.00
% 5.61/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
