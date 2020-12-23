%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:42 EST 2020

% Result     : Theorem 4.32s
% Output     : CNFRefutation 4.32s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 147 expanded)
%              Number of leaves         :   33 (  68 expanded)
%              Depth                    :    9
%              Number of atoms          :  151 ( 392 expanded)
%              Number of equality atoms :  122 ( 312 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_134,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & ~ ! [D] :
                ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
               => ( D != k5_mcart_1(A,B,C,D)
                  & D != k6_mcart_1(A,B,C,D)
                  & D != k7_mcart_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).

tff(f_106,axiom,(
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

tff(f_43,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

tff(f_70,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_16,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_93,plain,(
    ! [A_57,B_58] : ~ r2_hidden(A_57,k2_zfmisc_1(A_57,B_58)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_96,plain,(
    ! [A_6] : ~ r2_hidden(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_93])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_50,plain,(
    m1_subset_1('#skF_7',k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1741,plain,(
    ! [A_387,B_388,C_389,D_390] :
      ( k7_mcart_1(A_387,B_388,C_389,D_390) = k2_mcart_1(D_390)
      | ~ m1_subset_1(D_390,k3_zfmisc_1(A_387,B_388,C_389))
      | k1_xboole_0 = C_389
      | k1_xboole_0 = B_388
      | k1_xboole_0 = A_387 ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1756,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = k2_mcart_1('#skF_7')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_1741])).

tff(c_1762,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = k2_mcart_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_54,c_52,c_1756])).

tff(c_920,plain,(
    ! [A_199,B_200,C_201] : k4_tarski(k4_tarski(A_199,B_200),C_201) = k3_mcart_1(A_199,B_200,C_201) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_46,plain,(
    ! [A_45,B_46] : k2_mcart_1(k4_tarski(A_45,B_46)) = B_46 ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_26,plain,(
    ! [B_19,C_20] : k2_mcart_1(k4_tarski(B_19,C_20)) != k4_tarski(B_19,C_20) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_58,plain,(
    ! [B_19,C_20] : k4_tarski(B_19,C_20) != C_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_26])).

tff(c_938,plain,(
    ! [A_199,B_200,C_201] : k3_mcart_1(A_199,B_200,C_201) != C_201 ),
    inference(superposition,[status(thm),theory(equality)],[c_920,c_58])).

tff(c_578,plain,(
    ! [A_154,B_155,C_156,D_157] :
      ( k7_mcart_1(A_154,B_155,C_156,D_157) = k2_mcart_1(D_157)
      | ~ m1_subset_1(D_157,k3_zfmisc_1(A_154,B_155,C_156))
      | k1_xboole_0 = C_156
      | k1_xboole_0 = B_155
      | k1_xboole_0 = A_154 ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_593,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = k2_mcart_1('#skF_7')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_578])).

tff(c_599,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = k2_mcart_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_54,c_52,c_593])).

tff(c_48,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7'
    | k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7'
    | k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_190,plain,(
    k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_716,plain,(
    ! [A_186,B_187,C_188,D_189] :
      ( k3_mcart_1(k5_mcart_1(A_186,B_187,C_188,D_189),k6_mcart_1(A_186,B_187,C_188,D_189),k7_mcart_1(A_186,B_187,C_188,D_189)) = D_189
      | ~ m1_subset_1(D_189,k3_zfmisc_1(A_186,B_187,C_188))
      | k1_xboole_0 = C_188
      | k1_xboole_0 = B_187
      | k1_xboole_0 = A_186 ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_761,plain,
    ( k3_mcart_1('#skF_7',k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7')) = '#skF_7'
    | ~ m1_subset_1('#skF_7',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_716])).

tff(c_768,plain,
    ( k3_mcart_1('#skF_7',k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k2_mcart_1('#skF_7')) = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_599,c_761])).

tff(c_769,plain,(
    k3_mcart_1('#skF_7',k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k2_mcart_1('#skF_7')) = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_54,c_52,c_768])).

tff(c_30,plain,(
    ! [A_21] :
      ( r2_hidden('#skF_3'(A_21),A_21)
      | k1_xboole_0 = A_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_117,plain,(
    ! [C_63,A_64] :
      ( C_63 = A_64
      | ~ r2_hidden(C_63,k1_tarski(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_125,plain,(
    ! [A_64] :
      ( '#skF_3'(k1_tarski(A_64)) = A_64
      | k1_tarski(A_64) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_117])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_327,plain,(
    ! [C_107,A_108,D_109,E_110] :
      ( ~ r2_hidden(C_107,A_108)
      | k3_mcart_1(C_107,D_109,E_110) != '#skF_3'(A_108)
      | k1_xboole_0 = A_108 ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_338,plain,(
    ! [C_114,D_115,E_116] :
      ( k3_mcart_1(C_114,D_115,E_116) != '#skF_3'(k1_tarski(C_114))
      | k1_tarski(C_114) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_327])).

tff(c_341,plain,(
    ! [A_64,D_115,E_116] :
      ( k3_mcart_1(A_64,D_115,E_116) != A_64
      | k1_tarski(A_64) = k1_xboole_0
      | k1_tarski(A_64) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_338])).

tff(c_806,plain,(
    k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_769,c_341])).

tff(c_833,plain,(
    r2_hidden('#skF_7',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_806,c_4])).

tff(c_843,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_833])).

tff(c_844,plain,
    ( k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7'
    | k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_915,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_844])).

tff(c_1375,plain,(
    ! [A_309,B_310,C_311,D_312] :
      ( k3_mcart_1(k5_mcart_1(A_309,B_310,C_311,D_312),k6_mcart_1(A_309,B_310,C_311,D_312),k7_mcart_1(A_309,B_310,C_311,D_312)) = D_312
      | ~ m1_subset_1(D_312,k3_zfmisc_1(A_309,B_310,C_311))
      | k1_xboole_0 = C_311
      | k1_xboole_0 = B_310
      | k1_xboole_0 = A_309 ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1417,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_7') = '#skF_7'
    | ~ m1_subset_1('#skF_7',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_915,c_1375])).

tff(c_1421,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_7') = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1417])).

tff(c_1423,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_54,c_52,c_938,c_1421])).

tff(c_1424,plain,(
    k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_844])).

tff(c_1856,plain,(
    ! [A_407,B_408,C_409,D_410] :
      ( k3_mcart_1(k5_mcart_1(A_407,B_408,C_409,D_410),k6_mcart_1(A_407,B_408,C_409,D_410),k7_mcart_1(A_407,B_408,C_409,D_410)) = D_410
      | ~ m1_subset_1(D_410,k3_zfmisc_1(A_407,B_408,C_409))
      | k1_xboole_0 = C_409
      | k1_xboole_0 = B_408
      | k1_xboole_0 = A_407 ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1898,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_7',k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7')) = '#skF_7'
    | ~ m1_subset_1('#skF_7',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1424,c_1856])).

tff(c_1905,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_7',k2_mcart_1('#skF_7')) = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1762,c_1898])).

tff(c_1906,plain,(
    k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_7',k2_mcart_1('#skF_7')) = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_54,c_52,c_1905])).

tff(c_1457,plain,(
    ! [D_316,A_317,C_318,E_319] :
      ( ~ r2_hidden(D_316,A_317)
      | k3_mcart_1(C_318,D_316,E_319) != '#skF_3'(A_317)
      | k1_xboole_0 = A_317 ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1489,plain,(
    ! [C_337,C_338,E_339] :
      ( k3_mcart_1(C_337,C_338,E_339) != '#skF_3'(k1_tarski(C_338))
      | k1_tarski(C_338) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_1457])).

tff(c_1492,plain,(
    ! [C_337,A_64,E_339] :
      ( k3_mcart_1(C_337,A_64,E_339) != A_64
      | k1_tarski(A_64) = k1_xboole_0
      | k1_tarski(A_64) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_1489])).

tff(c_1940,plain,(
    k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1906,c_1492])).

tff(c_1967,plain,(
    r2_hidden('#skF_7',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1940,c_4])).

tff(c_1977,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_1967])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n011.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 20:27:12 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.32/1.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.32/1.83  
% 4.32/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.32/1.83  %$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 4.32/1.83  
% 4.32/1.83  %Foreground sorts:
% 4.32/1.83  
% 4.32/1.83  
% 4.32/1.83  %Background operators:
% 4.32/1.83  
% 4.32/1.83  
% 4.32/1.83  %Foreground operators:
% 4.32/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.32/1.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.32/1.83  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.32/1.83  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.32/1.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.32/1.83  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 4.32/1.83  tff('#skF_7', type, '#skF_7': $i).
% 4.32/1.83  tff('#skF_5', type, '#skF_5': $i).
% 4.32/1.83  tff('#skF_6', type, '#skF_6': $i).
% 4.32/1.83  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 4.32/1.83  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 4.32/1.83  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 4.32/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.32/1.83  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 4.32/1.83  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.32/1.83  tff('#skF_4', type, '#skF_4': $i).
% 4.32/1.83  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.32/1.83  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 4.32/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.32/1.83  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.32/1.83  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 4.32/1.83  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.32/1.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.32/1.83  
% 4.32/1.85  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.32/1.85  tff(f_41, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 4.32/1.85  tff(f_134, negated_conjecture, ~(![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => ((~(D = k5_mcart_1(A, B, C, D)) & ~(D = k6_mcart_1(A, B, C, D))) & ~(D = k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_mcart_1)).
% 4.32/1.85  tff(f_106, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 4.32/1.85  tff(f_43, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 4.32/1.85  tff(f_110, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 4.32/1.85  tff(f_54, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 4.32/1.85  tff(f_86, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_mcart_1)).
% 4.32/1.85  tff(f_70, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 4.32/1.85  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 4.32/1.85  tff(c_16, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.32/1.85  tff(c_93, plain, (![A_57, B_58]: (~r2_hidden(A_57, k2_zfmisc_1(A_57, B_58)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.32/1.85  tff(c_96, plain, (![A_6]: (~r2_hidden(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_93])).
% 4.32/1.85  tff(c_56, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.32/1.85  tff(c_54, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.32/1.85  tff(c_52, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.32/1.85  tff(c_50, plain, (m1_subset_1('#skF_7', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.32/1.85  tff(c_1741, plain, (![A_387, B_388, C_389, D_390]: (k7_mcart_1(A_387, B_388, C_389, D_390)=k2_mcart_1(D_390) | ~m1_subset_1(D_390, k3_zfmisc_1(A_387, B_388, C_389)) | k1_xboole_0=C_389 | k1_xboole_0=B_388 | k1_xboole_0=A_387)), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.32/1.85  tff(c_1756, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')=k2_mcart_1('#skF_7') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_50, c_1741])).
% 4.32/1.85  tff(c_1762, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')=k2_mcart_1('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_56, c_54, c_52, c_1756])).
% 4.32/1.85  tff(c_920, plain, (![A_199, B_200, C_201]: (k4_tarski(k4_tarski(A_199, B_200), C_201)=k3_mcart_1(A_199, B_200, C_201))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.32/1.85  tff(c_46, plain, (![A_45, B_46]: (k2_mcart_1(k4_tarski(A_45, B_46))=B_46)), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.32/1.85  tff(c_26, plain, (![B_19, C_20]: (k2_mcart_1(k4_tarski(B_19, C_20))!=k4_tarski(B_19, C_20))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.32/1.85  tff(c_58, plain, (![B_19, C_20]: (k4_tarski(B_19, C_20)!=C_20)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_26])).
% 4.32/1.85  tff(c_938, plain, (![A_199, B_200, C_201]: (k3_mcart_1(A_199, B_200, C_201)!=C_201)), inference(superposition, [status(thm), theory('equality')], [c_920, c_58])).
% 4.32/1.85  tff(c_578, plain, (![A_154, B_155, C_156, D_157]: (k7_mcart_1(A_154, B_155, C_156, D_157)=k2_mcart_1(D_157) | ~m1_subset_1(D_157, k3_zfmisc_1(A_154, B_155, C_156)) | k1_xboole_0=C_156 | k1_xboole_0=B_155 | k1_xboole_0=A_154)), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.32/1.85  tff(c_593, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')=k2_mcart_1('#skF_7') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_50, c_578])).
% 4.32/1.85  tff(c_599, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')=k2_mcart_1('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_56, c_54, c_52, c_593])).
% 4.32/1.85  tff(c_48, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7' | k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7' | k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.32/1.85  tff(c_190, plain, (k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(splitLeft, [status(thm)], [c_48])).
% 4.32/1.85  tff(c_716, plain, (![A_186, B_187, C_188, D_189]: (k3_mcart_1(k5_mcart_1(A_186, B_187, C_188, D_189), k6_mcart_1(A_186, B_187, C_188, D_189), k7_mcart_1(A_186, B_187, C_188, D_189))=D_189 | ~m1_subset_1(D_189, k3_zfmisc_1(A_186, B_187, C_188)) | k1_xboole_0=C_188 | k1_xboole_0=B_187 | k1_xboole_0=A_186)), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.32/1.85  tff(c_761, plain, (k3_mcart_1('#skF_7', k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'))='#skF_7' | ~m1_subset_1('#skF_7', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_190, c_716])).
% 4.32/1.85  tff(c_768, plain, (k3_mcart_1('#skF_7', k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k2_mcart_1('#skF_7'))='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_599, c_761])).
% 4.32/1.85  tff(c_769, plain, (k3_mcart_1('#skF_7', k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k2_mcart_1('#skF_7'))='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_56, c_54, c_52, c_768])).
% 4.32/1.85  tff(c_30, plain, (![A_21]: (r2_hidden('#skF_3'(A_21), A_21) | k1_xboole_0=A_21)), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.32/1.85  tff(c_117, plain, (![C_63, A_64]: (C_63=A_64 | ~r2_hidden(C_63, k1_tarski(A_64)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.32/1.85  tff(c_125, plain, (![A_64]: ('#skF_3'(k1_tarski(A_64))=A_64 | k1_tarski(A_64)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_117])).
% 4.32/1.85  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.32/1.85  tff(c_327, plain, (![C_107, A_108, D_109, E_110]: (~r2_hidden(C_107, A_108) | k3_mcart_1(C_107, D_109, E_110)!='#skF_3'(A_108) | k1_xboole_0=A_108)), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.32/1.85  tff(c_338, plain, (![C_114, D_115, E_116]: (k3_mcart_1(C_114, D_115, E_116)!='#skF_3'(k1_tarski(C_114)) | k1_tarski(C_114)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_327])).
% 4.32/1.85  tff(c_341, plain, (![A_64, D_115, E_116]: (k3_mcart_1(A_64, D_115, E_116)!=A_64 | k1_tarski(A_64)=k1_xboole_0 | k1_tarski(A_64)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_125, c_338])).
% 4.32/1.85  tff(c_806, plain, (k1_tarski('#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_769, c_341])).
% 4.32/1.85  tff(c_833, plain, (r2_hidden('#skF_7', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_806, c_4])).
% 4.32/1.85  tff(c_843, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_833])).
% 4.32/1.85  tff(c_844, plain, (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7' | k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(splitRight, [status(thm)], [c_48])).
% 4.32/1.85  tff(c_915, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(splitLeft, [status(thm)], [c_844])).
% 4.32/1.85  tff(c_1375, plain, (![A_309, B_310, C_311, D_312]: (k3_mcart_1(k5_mcart_1(A_309, B_310, C_311, D_312), k6_mcart_1(A_309, B_310, C_311, D_312), k7_mcart_1(A_309, B_310, C_311, D_312))=D_312 | ~m1_subset_1(D_312, k3_zfmisc_1(A_309, B_310, C_311)) | k1_xboole_0=C_311 | k1_xboole_0=B_310 | k1_xboole_0=A_309)), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.32/1.85  tff(c_1417, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_7')='#skF_7' | ~m1_subset_1('#skF_7', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_915, c_1375])).
% 4.32/1.85  tff(c_1421, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_7')='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1417])).
% 4.32/1.85  tff(c_1423, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_54, c_52, c_938, c_1421])).
% 4.32/1.85  tff(c_1424, plain, (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(splitRight, [status(thm)], [c_844])).
% 4.32/1.85  tff(c_1856, plain, (![A_407, B_408, C_409, D_410]: (k3_mcart_1(k5_mcart_1(A_407, B_408, C_409, D_410), k6_mcart_1(A_407, B_408, C_409, D_410), k7_mcart_1(A_407, B_408, C_409, D_410))=D_410 | ~m1_subset_1(D_410, k3_zfmisc_1(A_407, B_408, C_409)) | k1_xboole_0=C_409 | k1_xboole_0=B_408 | k1_xboole_0=A_407)), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.32/1.85  tff(c_1898, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_7', k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'))='#skF_7' | ~m1_subset_1('#skF_7', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1424, c_1856])).
% 4.32/1.85  tff(c_1905, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_7', k2_mcart_1('#skF_7'))='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1762, c_1898])).
% 4.32/1.85  tff(c_1906, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_7', k2_mcart_1('#skF_7'))='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_56, c_54, c_52, c_1905])).
% 4.32/1.85  tff(c_1457, plain, (![D_316, A_317, C_318, E_319]: (~r2_hidden(D_316, A_317) | k3_mcart_1(C_318, D_316, E_319)!='#skF_3'(A_317) | k1_xboole_0=A_317)), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.32/1.85  tff(c_1489, plain, (![C_337, C_338, E_339]: (k3_mcart_1(C_337, C_338, E_339)!='#skF_3'(k1_tarski(C_338)) | k1_tarski(C_338)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_1457])).
% 4.32/1.85  tff(c_1492, plain, (![C_337, A_64, E_339]: (k3_mcart_1(C_337, A_64, E_339)!=A_64 | k1_tarski(A_64)=k1_xboole_0 | k1_tarski(A_64)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_125, c_1489])).
% 4.32/1.85  tff(c_1940, plain, (k1_tarski('#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1906, c_1492])).
% 4.32/1.85  tff(c_1967, plain, (r2_hidden('#skF_7', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1940, c_4])).
% 4.32/1.85  tff(c_1977, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_1967])).
% 4.32/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.32/1.85  
% 4.32/1.85  Inference rules
% 4.32/1.85  ----------------------
% 4.32/1.85  #Ref     : 0
% 4.32/1.85  #Sup     : 478
% 4.32/1.85  #Fact    : 0
% 4.32/1.85  #Define  : 0
% 4.32/1.85  #Split   : 2
% 4.32/1.85  #Chain   : 0
% 4.32/1.85  #Close   : 0
% 4.32/1.85  
% 4.32/1.85  Ordering : KBO
% 4.32/1.85  
% 4.32/1.85  Simplification rules
% 4.32/1.85  ----------------------
% 4.32/1.85  #Subsume      : 107
% 4.32/1.85  #Demod        : 203
% 4.32/1.85  #Tautology    : 223
% 4.32/1.85  #SimpNegUnit  : 19
% 4.32/1.85  #BackRed      : 4
% 4.32/1.85  
% 4.32/1.85  #Partial instantiations: 0
% 4.32/1.85  #Strategies tried      : 1
% 4.32/1.85  
% 4.32/1.85  Timing (in seconds)
% 4.32/1.85  ----------------------
% 4.32/1.85  Preprocessing        : 0.35
% 4.32/1.85  Parsing              : 0.18
% 4.32/1.85  CNF conversion       : 0.03
% 4.32/1.85  Main loop            : 0.72
% 4.32/1.85  Inferencing          : 0.28
% 4.32/1.85  Reduction            : 0.22
% 4.32/1.85  Demodulation         : 0.15
% 4.32/1.85  BG Simplification    : 0.04
% 4.32/1.85  Subsumption          : 0.12
% 4.32/1.85  Abstraction          : 0.04
% 4.32/1.85  MUC search           : 0.00
% 4.32/1.85  Cooper               : 0.00
% 4.32/1.85  Total                : 1.11
% 4.32/1.85  Index Insertion      : 0.00
% 4.32/1.86  Index Deletion       : 0.00
% 4.32/1.86  Index Matching       : 0.00
% 4.32/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
