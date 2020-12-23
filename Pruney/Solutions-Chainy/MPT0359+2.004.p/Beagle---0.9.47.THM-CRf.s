%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:09 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 246 expanded)
%              Number of leaves         :   39 (  96 expanded)
%              Depth                    :   14
%              Number of atoms          :  108 ( 320 expanded)
%              Number of equality atoms :   58 ( 173 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_59,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_71,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_82,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_65,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_55,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_16,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_30,plain,(
    ! [A_25] : k1_subset_1(A_25) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_32,plain,(
    ! [A_26] : k2_subset_1(A_26) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_40,plain,(
    ! [A_32] : k3_subset_1(A_32,k1_subset_1(A_32)) = k2_subset_1(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_57,plain,(
    ! [A_32] : k3_subset_1(A_32,k1_subset_1(A_32)) = A_32 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_40])).

tff(c_61,plain,(
    ! [A_32] : k3_subset_1(A_32,k1_xboole_0) = A_32 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_57])).

tff(c_46,plain,(
    ! [A_37] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_890,plain,(
    ! [A_93,B_94] :
      ( k3_subset_1(A_93,k3_subset_1(A_93,B_94)) = B_94
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_892,plain,(
    ! [A_37] : k3_subset_1(A_37,k3_subset_1(A_37,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_890])).

tff(c_896,plain,(
    ! [A_37] : k3_subset_1(A_37,A_37) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_892])).

tff(c_56,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | k2_subset_1('#skF_1') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_59,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_56])).

tff(c_93,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_59])).

tff(c_50,plain,
    ( k2_subset_1('#skF_1') != '#skF_2'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_60,plain,
    ( '#skF_2' != '#skF_1'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_50])).

tff(c_283,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_93,c_93,c_60])).

tff(c_898,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_896,c_283])).

tff(c_901,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_898])).

tff(c_903,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_59])).

tff(c_48,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_36,plain,(
    ! [A_29] : m1_subset_1(k2_subset_1(A_29),k1_zfmisc_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_58,plain,(
    ! [A_29] : m1_subset_1(A_29,k1_zfmisc_1(A_29)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_36])).

tff(c_2011,plain,(
    ! [A_151,B_152] :
      ( k3_subset_1(A_151,k3_subset_1(A_151,B_152)) = B_152
      | ~ m1_subset_1(B_152,k1_zfmisc_1(A_151)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2015,plain,(
    ! [A_37] : k3_subset_1(A_37,k3_subset_1(A_37,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_2011])).

tff(c_2020,plain,(
    ! [A_37] : k3_subset_1(A_37,A_37) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_2015])).

tff(c_2180,plain,(
    ! [B_156,C_157,A_158] :
      ( r1_tarski(B_156,C_157)
      | ~ r1_tarski(k3_subset_1(A_158,C_157),k3_subset_1(A_158,B_156))
      | ~ m1_subset_1(C_157,k1_zfmisc_1(A_158))
      | ~ m1_subset_1(B_156,k1_zfmisc_1(A_158)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2189,plain,(
    ! [B_156,A_37] :
      ( r1_tarski(B_156,A_37)
      | ~ r1_tarski(k1_xboole_0,k3_subset_1(A_37,B_156))
      | ~ m1_subset_1(A_37,k1_zfmisc_1(A_37))
      | ~ m1_subset_1(B_156,k1_zfmisc_1(A_37)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2020,c_2180])).

tff(c_2213,plain,(
    ! [B_159,A_160] :
      ( r1_tarski(B_159,A_160)
      | ~ m1_subset_1(B_159,k1_zfmisc_1(A_160)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_16,c_2189])).

tff(c_2223,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_2213])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2236,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2223,c_14])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_972,plain,(
    ! [A_99,B_100] : k2_xboole_0(A_99,k3_xboole_0(A_99,B_100)) = A_99 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_981,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_972])).

tff(c_2246,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_2236,c_981])).

tff(c_22,plain,(
    ! [B_17,A_16] : k2_tarski(B_17,A_16) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1188,plain,(
    ! [A_110,B_111] : k3_tarski(k2_tarski(A_110,B_111)) = k2_xboole_0(A_110,B_111) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1219,plain,(
    ! [A_114,B_115] : k3_tarski(k2_tarski(A_114,B_115)) = k2_xboole_0(B_115,A_114) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1188])).

tff(c_28,plain,(
    ! [A_23,B_24] : k3_tarski(k2_tarski(A_23,B_24)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1225,plain,(
    ! [B_115,A_114] : k2_xboole_0(B_115,A_114) = k2_xboole_0(A_114,B_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_1219,c_28])).

tff(c_1782,plain,(
    ! [A_144,B_145] :
      ( k4_xboole_0(A_144,B_145) = k3_subset_1(A_144,B_145)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(A_144)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1792,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1782])).

tff(c_20,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1811,plain,(
    k5_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1792,c_20])).

tff(c_1820,plain,(
    k5_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1225,c_1811])).

tff(c_2317,plain,(
    k5_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2246,c_1820])).

tff(c_902,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_59])).

tff(c_1015,plain,(
    ! [A_103,B_104] :
      ( k3_xboole_0(A_103,B_104) = A_103
      | ~ r1_tarski(A_103,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1028,plain,(
    k3_xboole_0(k3_subset_1('#skF_1','#skF_2'),'#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_902,c_1015])).

tff(c_1419,plain,(
    ! [A_125,B_126] : k5_xboole_0(A_125,k3_xboole_0(A_125,B_126)) = k4_xboole_0(A_125,B_126) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1572,plain,(
    ! [A_131,B_132] : k5_xboole_0(A_131,k3_xboole_0(B_132,A_131)) = k4_xboole_0(A_131,B_132) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1419])).

tff(c_1603,plain,(
    k5_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k4_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1028,c_1572])).

tff(c_2443,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2317,c_1603])).

tff(c_18,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1357,plain,(
    ! [B_119,A_120] :
      ( B_119 = A_120
      | ~ r1_tarski(B_119,A_120)
      | ~ r1_tarski(A_120,B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1367,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,k4_xboole_0(A_12,B_13)) ) ),
    inference(resolution,[status(thm)],[c_18,c_1357])).

tff(c_2447,plain,
    ( k4_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2443,c_1367])).

tff(c_2466,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2223,c_2443,c_2447])).

tff(c_2468,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_903,c_2466])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:47:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.60/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/1.67  
% 3.60/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/1.67  %$ r1_tarski > m1_subset_1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.60/1.67  
% 3.60/1.67  %Foreground sorts:
% 3.60/1.67  
% 3.60/1.67  
% 3.60/1.67  %Background operators:
% 3.60/1.67  
% 3.60/1.67  
% 3.60/1.67  %Foreground operators:
% 3.60/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.60/1.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.60/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.60/1.67  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.60/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.60/1.67  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.60/1.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.60/1.67  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.60/1.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.60/1.67  tff('#skF_2', type, '#skF_2': $i).
% 3.60/1.67  tff('#skF_1', type, '#skF_1': $i).
% 3.60/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.60/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.60/1.67  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.60/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.60/1.67  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.60/1.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.60/1.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.60/1.67  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.60/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.60/1.67  
% 3.60/1.69  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.60/1.69  tff(f_57, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 3.60/1.69  tff(f_59, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.60/1.69  tff(f_71, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 3.60/1.69  tff(f_82, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.60/1.69  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.60/1.69  tff(f_89, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 3.60/1.69  tff(f_65, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.60/1.69  tff(f_80, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 3.60/1.69  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.60/1.69  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.60/1.69  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 3.60/1.69  tff(f_49, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.60/1.69  tff(f_55, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.60/1.69  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.60/1.69  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.60/1.69  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.60/1.69  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.60/1.69  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.60/1.69  tff(c_16, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.60/1.69  tff(c_30, plain, (![A_25]: (k1_subset_1(A_25)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.60/1.69  tff(c_32, plain, (![A_26]: (k2_subset_1(A_26)=A_26)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.60/1.69  tff(c_40, plain, (![A_32]: (k3_subset_1(A_32, k1_subset_1(A_32))=k2_subset_1(A_32))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.60/1.69  tff(c_57, plain, (![A_32]: (k3_subset_1(A_32, k1_subset_1(A_32))=A_32)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_40])).
% 3.60/1.69  tff(c_61, plain, (![A_32]: (k3_subset_1(A_32, k1_xboole_0)=A_32)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_57])).
% 3.60/1.69  tff(c_46, plain, (![A_37]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.60/1.69  tff(c_890, plain, (![A_93, B_94]: (k3_subset_1(A_93, k3_subset_1(A_93, B_94))=B_94 | ~m1_subset_1(B_94, k1_zfmisc_1(A_93)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.60/1.69  tff(c_892, plain, (![A_37]: (k3_subset_1(A_37, k3_subset_1(A_37, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_890])).
% 3.60/1.69  tff(c_896, plain, (![A_37]: (k3_subset_1(A_37, A_37)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_61, c_892])).
% 3.60/1.69  tff(c_56, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | k2_subset_1('#skF_1')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.60/1.69  tff(c_59, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_56])).
% 3.60/1.69  tff(c_93, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_59])).
% 3.60/1.69  tff(c_50, plain, (k2_subset_1('#skF_1')!='#skF_2' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.60/1.69  tff(c_60, plain, ('#skF_2'!='#skF_1' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_50])).
% 3.60/1.69  tff(c_283, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_93, c_93, c_60])).
% 3.60/1.69  tff(c_898, plain, (~r1_tarski(k1_xboole_0, '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_896, c_283])).
% 3.60/1.69  tff(c_901, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_898])).
% 3.60/1.69  tff(c_903, plain, ('#skF_2'!='#skF_1'), inference(splitRight, [status(thm)], [c_59])).
% 3.60/1.69  tff(c_48, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.60/1.69  tff(c_36, plain, (![A_29]: (m1_subset_1(k2_subset_1(A_29), k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.60/1.69  tff(c_58, plain, (![A_29]: (m1_subset_1(A_29, k1_zfmisc_1(A_29)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_36])).
% 3.60/1.69  tff(c_2011, plain, (![A_151, B_152]: (k3_subset_1(A_151, k3_subset_1(A_151, B_152))=B_152 | ~m1_subset_1(B_152, k1_zfmisc_1(A_151)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.60/1.69  tff(c_2015, plain, (![A_37]: (k3_subset_1(A_37, k3_subset_1(A_37, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_2011])).
% 3.60/1.69  tff(c_2020, plain, (![A_37]: (k3_subset_1(A_37, A_37)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_61, c_2015])).
% 3.60/1.69  tff(c_2180, plain, (![B_156, C_157, A_158]: (r1_tarski(B_156, C_157) | ~r1_tarski(k3_subset_1(A_158, C_157), k3_subset_1(A_158, B_156)) | ~m1_subset_1(C_157, k1_zfmisc_1(A_158)) | ~m1_subset_1(B_156, k1_zfmisc_1(A_158)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.60/1.69  tff(c_2189, plain, (![B_156, A_37]: (r1_tarski(B_156, A_37) | ~r1_tarski(k1_xboole_0, k3_subset_1(A_37, B_156)) | ~m1_subset_1(A_37, k1_zfmisc_1(A_37)) | ~m1_subset_1(B_156, k1_zfmisc_1(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_2020, c_2180])).
% 3.60/1.69  tff(c_2213, plain, (![B_159, A_160]: (r1_tarski(B_159, A_160) | ~m1_subset_1(B_159, k1_zfmisc_1(A_160)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_16, c_2189])).
% 3.60/1.69  tff(c_2223, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_2213])).
% 3.60/1.69  tff(c_14, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.60/1.69  tff(c_2236, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_2223, c_14])).
% 3.60/1.69  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.60/1.69  tff(c_972, plain, (![A_99, B_100]: (k2_xboole_0(A_99, k3_xboole_0(A_99, B_100))=A_99)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.60/1.69  tff(c_981, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k3_xboole_0(B_2, A_1))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_972])).
% 3.60/1.69  tff(c_2246, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_2236, c_981])).
% 3.60/1.69  tff(c_22, plain, (![B_17, A_16]: (k2_tarski(B_17, A_16)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.60/1.69  tff(c_1188, plain, (![A_110, B_111]: (k3_tarski(k2_tarski(A_110, B_111))=k2_xboole_0(A_110, B_111))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.60/1.69  tff(c_1219, plain, (![A_114, B_115]: (k3_tarski(k2_tarski(A_114, B_115))=k2_xboole_0(B_115, A_114))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1188])).
% 3.60/1.69  tff(c_28, plain, (![A_23, B_24]: (k3_tarski(k2_tarski(A_23, B_24))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.60/1.69  tff(c_1225, plain, (![B_115, A_114]: (k2_xboole_0(B_115, A_114)=k2_xboole_0(A_114, B_115))), inference(superposition, [status(thm), theory('equality')], [c_1219, c_28])).
% 3.60/1.69  tff(c_1782, plain, (![A_144, B_145]: (k4_xboole_0(A_144, B_145)=k3_subset_1(A_144, B_145) | ~m1_subset_1(B_145, k1_zfmisc_1(A_144)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.60/1.69  tff(c_1792, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_48, c_1782])).
% 3.60/1.69  tff(c_20, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.60/1.69  tff(c_1811, plain, (k5_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1792, c_20])).
% 3.60/1.69  tff(c_1820, plain, (k5_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1225, c_1811])).
% 3.60/1.69  tff(c_2317, plain, (k5_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2246, c_1820])).
% 3.60/1.69  tff(c_902, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_59])).
% 3.60/1.69  tff(c_1015, plain, (![A_103, B_104]: (k3_xboole_0(A_103, B_104)=A_103 | ~r1_tarski(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.60/1.69  tff(c_1028, plain, (k3_xboole_0(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_902, c_1015])).
% 3.60/1.69  tff(c_1419, plain, (![A_125, B_126]: (k5_xboole_0(A_125, k3_xboole_0(A_125, B_126))=k4_xboole_0(A_125, B_126))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.60/1.69  tff(c_1572, plain, (![A_131, B_132]: (k5_xboole_0(A_131, k3_xboole_0(B_132, A_131))=k4_xboole_0(A_131, B_132))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1419])).
% 3.60/1.69  tff(c_1603, plain, (k5_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k4_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1028, c_1572])).
% 3.60/1.69  tff(c_2443, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2317, c_1603])).
% 3.60/1.69  tff(c_18, plain, (![A_12, B_13]: (r1_tarski(k4_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.60/1.69  tff(c_1357, plain, (![B_119, A_120]: (B_119=A_120 | ~r1_tarski(B_119, A_120) | ~r1_tarski(A_120, B_119))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.60/1.69  tff(c_1367, plain, (![A_12, B_13]: (k4_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, k4_xboole_0(A_12, B_13)))), inference(resolution, [status(thm)], [c_18, c_1357])).
% 3.60/1.69  tff(c_2447, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_2' | ~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2443, c_1367])).
% 3.60/1.69  tff(c_2466, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2223, c_2443, c_2447])).
% 3.60/1.69  tff(c_2468, plain, $false, inference(negUnitSimplification, [status(thm)], [c_903, c_2466])).
% 3.60/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/1.69  
% 3.60/1.69  Inference rules
% 3.60/1.69  ----------------------
% 3.60/1.69  #Ref     : 0
% 3.60/1.69  #Sup     : 572
% 3.60/1.69  #Fact    : 0
% 3.60/1.69  #Define  : 0
% 3.60/1.69  #Split   : 4
% 3.60/1.69  #Chain   : 0
% 3.60/1.69  #Close   : 0
% 3.60/1.69  
% 3.60/1.69  Ordering : KBO
% 3.60/1.69  
% 3.60/1.69  Simplification rules
% 3.60/1.69  ----------------------
% 3.60/1.69  #Subsume      : 14
% 3.60/1.69  #Demod        : 320
% 3.60/1.69  #Tautology    : 463
% 3.60/1.69  #SimpNegUnit  : 2
% 3.60/1.69  #BackRed      : 10
% 3.60/1.69  
% 3.60/1.69  #Partial instantiations: 0
% 3.60/1.69  #Strategies tried      : 1
% 3.60/1.69  
% 3.60/1.69  Timing (in seconds)
% 3.60/1.69  ----------------------
% 3.60/1.69  Preprocessing        : 0.34
% 3.60/1.69  Parsing              : 0.18
% 3.60/1.69  CNF conversion       : 0.02
% 3.60/1.69  Main loop            : 0.57
% 3.60/1.69  Inferencing          : 0.21
% 3.60/1.69  Reduction            : 0.21
% 3.60/1.69  Demodulation         : 0.16
% 3.60/1.69  BG Simplification    : 0.02
% 3.60/1.69  Subsumption          : 0.09
% 3.60/1.69  Abstraction          : 0.03
% 3.60/1.69  MUC search           : 0.00
% 3.60/1.69  Cooper               : 0.00
% 3.60/1.69  Total                : 0.94
% 3.60/1.69  Index Insertion      : 0.00
% 3.60/1.69  Index Deletion       : 0.00
% 3.60/1.69  Index Matching       : 0.00
% 3.60/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
