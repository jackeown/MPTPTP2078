%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:42 EST 2020

% Result     : Theorem 7.47s
% Output     : CNFRefutation 7.74s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 286 expanded)
%              Number of leaves         :   44 ( 119 expanded)
%              Depth                    :   12
%              Number of atoms          :  206 ( 636 expanded)
%              Number of equality atoms :  158 ( 456 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_161,negated_conjecture,(
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

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_97,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_40,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_36,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_38,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_137,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_133,axiom,(
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

tff(f_113,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

tff(c_94,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_92,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_90,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_44,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,(
    ! [D_16,A_11] : r2_hidden(D_16,k2_tarski(A_11,D_16)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_68,plain,(
    ! [A_37] :
      ( r2_hidden('#skF_5'(A_37),A_37)
      | k1_xboole_0 = A_37 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_4058,plain,(
    ! [D_386,B_387,A_388] :
      ( r2_hidden(D_386,B_387)
      | ~ r2_hidden(D_386,k3_xboole_0(A_388,B_387)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_8037,plain,(
    ! [A_709,B_710] :
      ( r2_hidden('#skF_5'(k3_xboole_0(A_709,B_710)),B_710)
      | k3_xboole_0(A_709,B_710) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_68,c_4058])).

tff(c_24,plain,(
    ! [A_10] : k4_xboole_0(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_162,plain,(
    ! [C_80,B_81] : ~ r2_hidden(C_80,k4_xboole_0(B_81,k1_tarski(C_80))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_165,plain,(
    ! [C_80] : ~ r2_hidden(C_80,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_162])).

tff(c_8070,plain,(
    ! [A_709] : k3_xboole_0(A_709,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8037,c_165])).

tff(c_20,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4064,plain,(
    ! [A_389,B_390] : k4_xboole_0(A_389,k4_xboole_0(A_389,B_390)) = k3_xboole_0(A_389,B_390) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4083,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_4064])).

tff(c_8156,plain,(
    ! [A_716] : k4_xboole_0(A_716,A_716) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8070,c_4083])).

tff(c_56,plain,(
    ! [B_24,C_25,A_23] :
      ( ~ r2_hidden(B_24,C_25)
      | k4_xboole_0(k2_tarski(A_23,B_24),C_25) != k2_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_8162,plain,(
    ! [B_24,A_23] :
      ( ~ r2_hidden(B_24,k2_tarski(A_23,B_24))
      | k2_tarski(A_23,B_24) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8156,c_56])).

tff(c_8198,plain,(
    ! [A_717,B_718] : k2_tarski(A_717,B_718) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_8162])).

tff(c_8200,plain,(
    ! [A_17] : k1_tarski(A_17) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_8198])).

tff(c_7958,plain,(
    ! [D_688,B_689,A_690] :
      ( D_688 = B_689
      | D_688 = A_690
      | ~ r2_hidden(D_688,k2_tarski(A_690,B_689)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8012,plain,(
    ! [D_706,A_707] :
      ( D_706 = A_707
      | D_706 = A_707
      | ~ r2_hidden(D_706,k1_tarski(A_707)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_7958])).

tff(c_8020,plain,(
    ! [A_707] :
      ( '#skF_5'(k1_tarski(A_707)) = A_707
      | k1_tarski(A_707) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_68,c_8012])).

tff(c_8222,plain,(
    ! [A_707] : '#skF_5'(k1_tarski(A_707)) = A_707 ),
    inference(negUnitSimplification,[status(thm)],[c_8200,c_8020])).

tff(c_145,plain,(
    ! [A_78] : k2_tarski(A_78,A_78) = k1_tarski(A_78) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_30,plain,(
    ! [D_16,B_12] : r2_hidden(D_16,k2_tarski(D_16,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_151,plain,(
    ! [A_78] : r2_hidden(A_78,k1_tarski(A_78)) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_30])).

tff(c_8314,plain,(
    ! [D_730,A_731,C_732,E_733] :
      ( ~ r2_hidden(D_730,A_731)
      | k3_mcart_1(C_732,D_730,E_733) != '#skF_5'(A_731)
      | k1_xboole_0 = A_731 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_8322,plain,(
    ! [C_732,A_78,E_733] :
      ( k3_mcart_1(C_732,A_78,E_733) != '#skF_5'(k1_tarski(A_78))
      | k1_tarski(A_78) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_151,c_8314])).

tff(c_8331,plain,(
    ! [C_732,A_78,E_733] :
      ( k3_mcart_1(C_732,A_78,E_733) != A_78
      | k1_tarski(A_78) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8222,c_8322])).

tff(c_8332,plain,(
    ! [C_732,A_78,E_733] : k3_mcart_1(C_732,A_78,E_733) != A_78 ),
    inference(negUnitSimplification,[status(thm)],[c_8200,c_8331])).

tff(c_88,plain,(
    m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_4200,plain,(
    ! [A_401,B_402,C_403] : k4_tarski(k4_tarski(A_401,B_402),C_403) = k3_mcart_1(A_401,B_402,C_403) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_84,plain,(
    ! [A_61,B_62] : k2_mcart_1(k4_tarski(A_61,B_62)) = B_62 ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_64,plain,(
    ! [B_35,C_36] : k2_mcart_1(k4_tarski(B_35,C_36)) != k4_tarski(B_35,C_36) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_96,plain,(
    ! [B_35,C_36] : k4_tarski(B_35,C_36) != C_36 ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_64])).

tff(c_4218,plain,(
    ! [A_401,B_402,C_403] : k3_mcart_1(A_401,B_402,C_403) != C_403 ),
    inference(superposition,[status(thm),theory(equality)],[c_4200,c_96])).

tff(c_188,plain,(
    ! [D_86,B_87,A_88] :
      ( r2_hidden(D_86,B_87)
      | ~ r2_hidden(D_86,k3_xboole_0(A_88,B_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_484,plain,(
    ! [A_134,B_135] :
      ( r2_hidden('#skF_5'(k3_xboole_0(A_134,B_135)),B_135)
      | k3_xboole_0(A_134,B_135) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_68,c_188])).

tff(c_520,plain,(
    ! [A_134] : k3_xboole_0(A_134,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_484,c_165])).

tff(c_194,plain,(
    ! [A_89,B_90] : k4_xboole_0(A_89,k4_xboole_0(A_89,B_90)) = k3_xboole_0(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_213,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_194])).

tff(c_540,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_520,c_213])).

tff(c_651,plain,(
    ! [B_143,C_144,A_145] :
      ( ~ r2_hidden(B_143,C_144)
      | k4_xboole_0(k2_tarski(A_145,B_143),C_144) != k2_tarski(A_145,B_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_655,plain,(
    ! [B_143,A_145] :
      ( ~ r2_hidden(B_143,k2_tarski(A_145,B_143))
      | k2_tarski(A_145,B_143) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_540,c_651])).

tff(c_676,plain,(
    ! [A_146,B_147] : k2_tarski(A_146,B_147) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_655])).

tff(c_678,plain,(
    ! [A_17] : k1_tarski(A_17) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_676])).

tff(c_340,plain,(
    ! [D_104,B_105,A_106] :
      ( D_104 = B_105
      | D_104 = A_106
      | ~ r2_hidden(D_104,k2_tarski(A_106,B_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_359,plain,(
    ! [D_107,A_108] :
      ( D_107 = A_108
      | D_107 = A_108
      | ~ r2_hidden(D_107,k1_tarski(A_108)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_340])).

tff(c_367,plain,(
    ! [A_108] :
      ( '#skF_5'(k1_tarski(A_108)) = A_108
      | k1_tarski(A_108) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_68,c_359])).

tff(c_679,plain,(
    ! [A_108] : '#skF_5'(k1_tarski(A_108)) = A_108 ),
    inference(negUnitSimplification,[status(thm)],[c_678,c_367])).

tff(c_681,plain,(
    ! [A_149] : '#skF_5'(k1_tarski(A_149)) = A_149 ),
    inference(negUnitSimplification,[status(thm)],[c_678,c_367])).

tff(c_422,plain,(
    ! [C_122,A_123,D_124,E_125] :
      ( ~ r2_hidden(C_122,A_123)
      | k3_mcart_1(C_122,D_124,E_125) != '#skF_5'(A_123)
      | k1_xboole_0 = A_123 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_431,plain,(
    ! [A_37,D_124,E_125] :
      ( k3_mcart_1('#skF_5'(A_37),D_124,E_125) != '#skF_5'(A_37)
      | k1_xboole_0 = A_37 ) ),
    inference(resolution,[status(thm)],[c_68,c_422])).

tff(c_687,plain,(
    ! [A_149,D_124,E_125] :
      ( k3_mcart_1(A_149,D_124,E_125) != '#skF_5'(k1_tarski(A_149))
      | k1_tarski(A_149) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_681,c_431])).

tff(c_695,plain,(
    ! [A_149,D_124,E_125] :
      ( k3_mcart_1(A_149,D_124,E_125) != A_149
      | k1_tarski(A_149) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_679,c_687])).

tff(c_696,plain,(
    ! [A_149,D_124,E_125] : k3_mcart_1(A_149,D_124,E_125) != A_149 ),
    inference(negUnitSimplification,[status(thm)],[c_678,c_695])).

tff(c_86,plain,
    ( k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9'
    | k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9'
    | k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_183,plain,(
    k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_2143,plain,(
    ! [A_297,B_298,C_299,D_300] :
      ( k7_mcart_1(A_297,B_298,C_299,D_300) = k2_mcart_1(D_300)
      | ~ m1_subset_1(D_300,k3_zfmisc_1(A_297,B_298,C_299))
      | k1_xboole_0 = C_299
      | k1_xboole_0 = B_298
      | k1_xboole_0 = A_297 ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2149,plain,
    ( k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_88,c_2143])).

tff(c_2152,plain,(
    k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = k2_mcart_1('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_92,c_90,c_2149])).

tff(c_3989,plain,(
    ! [A_382,B_383,C_384,D_385] :
      ( k3_mcart_1(k5_mcart_1(A_382,B_383,C_384,D_385),k6_mcart_1(A_382,B_383,C_384,D_385),k7_mcart_1(A_382,B_383,C_384,D_385)) = D_385
      | ~ m1_subset_1(D_385,k3_zfmisc_1(A_382,B_383,C_384))
      | k1_xboole_0 = C_384
      | k1_xboole_0 = B_383
      | k1_xboole_0 = A_382 ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_4046,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k2_mcart_1('#skF_9')) = '#skF_9'
    | ~ m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_2152,c_3989])).

tff(c_4053,plain,
    ( k3_mcart_1('#skF_9',k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k2_mcart_1('#skF_9')) = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_183,c_4046])).

tff(c_4055,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_92,c_90,c_696,c_4053])).

tff(c_4056,plain,
    ( k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9'
    | k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_4153,plain,(
    k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_4056])).

tff(c_7819,plain,(
    ! [A_677,B_678,C_679,D_680] :
      ( k3_mcart_1(k5_mcart_1(A_677,B_678,C_679,D_680),k6_mcart_1(A_677,B_678,C_679,D_680),k7_mcart_1(A_677,B_678,C_679,D_680)) = D_680
      | ~ m1_subset_1(D_680,k3_zfmisc_1(A_677,B_678,C_679))
      | k1_xboole_0 = C_679
      | k1_xboole_0 = B_678
      | k1_xboole_0 = A_677 ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_7876,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9') = '#skF_9'
    | ~ m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_4153,c_7819])).

tff(c_7880,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9') = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_7876])).

tff(c_7882,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_92,c_90,c_4218,c_7880])).

tff(c_7883,plain,(
    k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_4056])).

tff(c_9999,plain,(
    ! [A_894,B_895,C_896,D_897] :
      ( k7_mcart_1(A_894,B_895,C_896,D_897) = k2_mcart_1(D_897)
      | ~ m1_subset_1(D_897,k3_zfmisc_1(A_894,B_895,C_896))
      | k1_xboole_0 = C_896
      | k1_xboole_0 = B_895
      | k1_xboole_0 = A_894 ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_10005,plain,
    ( k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_88,c_9999])).

tff(c_10008,plain,(
    k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = k2_mcart_1('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_92,c_90,c_10005])).

tff(c_11574,plain,(
    ! [A_962,B_963,C_964,D_965] :
      ( k3_mcart_1(k5_mcart_1(A_962,B_963,C_964,D_965),k6_mcart_1(A_962,B_963,C_964,D_965),k7_mcart_1(A_962,B_963,C_964,D_965)) = D_965
      | ~ m1_subset_1(D_965,k3_zfmisc_1(A_962,B_963,C_964))
      | k1_xboole_0 = C_964
      | k1_xboole_0 = B_963
      | k1_xboole_0 = A_962 ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_11631,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k2_mcart_1('#skF_9')) = '#skF_9'
    | ~ m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_10008,c_11574])).

tff(c_11638,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9',k2_mcart_1('#skF_9')) = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_7883,c_11631])).

tff(c_11640,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_92,c_90,c_8332,c_11638])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n012.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 20:11:22 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.47/2.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.47/2.73  
% 7.47/2.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.47/2.73  %$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3
% 7.47/2.73  
% 7.47/2.73  %Foreground sorts:
% 7.47/2.73  
% 7.47/2.73  
% 7.47/2.73  %Background operators:
% 7.47/2.73  
% 7.47/2.73  
% 7.47/2.73  %Foreground operators:
% 7.47/2.73  tff('#skF_5', type, '#skF_5': $i > $i).
% 7.47/2.73  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.47/2.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.47/2.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.47/2.73  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.47/2.73  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.47/2.73  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.47/2.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.47/2.73  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 7.47/2.73  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 7.47/2.73  tff('#skF_7', type, '#skF_7': $i).
% 7.47/2.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.47/2.73  tff('#skF_6', type, '#skF_6': $i).
% 7.47/2.73  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.47/2.73  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.47/2.73  tff('#skF_9', type, '#skF_9': $i).
% 7.47/2.73  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 7.47/2.73  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 7.47/2.73  tff('#skF_8', type, '#skF_8': $i).
% 7.47/2.73  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 7.47/2.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.47/2.73  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 7.47/2.73  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.47/2.73  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.47/2.73  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 7.47/2.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.47/2.73  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 7.47/2.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.47/2.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.47/2.73  
% 7.74/2.75  tff(f_161, negated_conjecture, ~(![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => ((~(D = k5_mcart_1(A, B, C, D)) & ~(D = k6_mcart_1(A, B, C, D))) & ~(D = k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_mcart_1)).
% 7.74/2.75  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 7.74/2.75  tff(f_49, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 7.74/2.75  tff(f_97, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 7.74/2.75  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 7.74/2.75  tff(f_40, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 7.74/2.75  tff(f_60, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 7.74/2.75  tff(f_36, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 7.74/2.75  tff(f_38, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.74/2.75  tff(f_68, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 7.74/2.75  tff(f_70, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 7.74/2.75  tff(f_137, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 7.74/2.75  tff(f_81, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 7.74/2.75  tff(f_133, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 7.74/2.75  tff(f_113, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_mcart_1)).
% 7.74/2.75  tff(c_94, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.74/2.75  tff(c_92, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.74/2.75  tff(c_90, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.74/2.75  tff(c_44, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.74/2.75  tff(c_28, plain, (![D_16, A_11]: (r2_hidden(D_16, k2_tarski(A_11, D_16)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.74/2.75  tff(c_68, plain, (![A_37]: (r2_hidden('#skF_5'(A_37), A_37) | k1_xboole_0=A_37)), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.74/2.75  tff(c_4058, plain, (![D_386, B_387, A_388]: (r2_hidden(D_386, B_387) | ~r2_hidden(D_386, k3_xboole_0(A_388, B_387)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.74/2.75  tff(c_8037, plain, (![A_709, B_710]: (r2_hidden('#skF_5'(k3_xboole_0(A_709, B_710)), B_710) | k3_xboole_0(A_709, B_710)=k1_xboole_0)), inference(resolution, [status(thm)], [c_68, c_4058])).
% 7.74/2.75  tff(c_24, plain, (![A_10]: (k4_xboole_0(k1_xboole_0, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.74/2.75  tff(c_162, plain, (![C_80, B_81]: (~r2_hidden(C_80, k4_xboole_0(B_81, k1_tarski(C_80))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.74/2.75  tff(c_165, plain, (![C_80]: (~r2_hidden(C_80, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_162])).
% 7.74/2.75  tff(c_8070, plain, (![A_709]: (k3_xboole_0(A_709, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8037, c_165])).
% 7.74/2.75  tff(c_20, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.74/2.75  tff(c_4064, plain, (![A_389, B_390]: (k4_xboole_0(A_389, k4_xboole_0(A_389, B_390))=k3_xboole_0(A_389, B_390))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.74/2.75  tff(c_4083, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_4064])).
% 7.74/2.75  tff(c_8156, plain, (![A_716]: (k4_xboole_0(A_716, A_716)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8070, c_4083])).
% 7.74/2.75  tff(c_56, plain, (![B_24, C_25, A_23]: (~r2_hidden(B_24, C_25) | k4_xboole_0(k2_tarski(A_23, B_24), C_25)!=k2_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.74/2.75  tff(c_8162, plain, (![B_24, A_23]: (~r2_hidden(B_24, k2_tarski(A_23, B_24)) | k2_tarski(A_23, B_24)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8156, c_56])).
% 7.74/2.75  tff(c_8198, plain, (![A_717, B_718]: (k2_tarski(A_717, B_718)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_8162])).
% 7.74/2.75  tff(c_8200, plain, (![A_17]: (k1_tarski(A_17)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_44, c_8198])).
% 7.74/2.75  tff(c_7958, plain, (![D_688, B_689, A_690]: (D_688=B_689 | D_688=A_690 | ~r2_hidden(D_688, k2_tarski(A_690, B_689)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.74/2.75  tff(c_8012, plain, (![D_706, A_707]: (D_706=A_707 | D_706=A_707 | ~r2_hidden(D_706, k1_tarski(A_707)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_7958])).
% 7.74/2.75  tff(c_8020, plain, (![A_707]: ('#skF_5'(k1_tarski(A_707))=A_707 | k1_tarski(A_707)=k1_xboole_0)), inference(resolution, [status(thm)], [c_68, c_8012])).
% 7.74/2.75  tff(c_8222, plain, (![A_707]: ('#skF_5'(k1_tarski(A_707))=A_707)), inference(negUnitSimplification, [status(thm)], [c_8200, c_8020])).
% 7.74/2.75  tff(c_145, plain, (![A_78]: (k2_tarski(A_78, A_78)=k1_tarski(A_78))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.74/2.75  tff(c_30, plain, (![D_16, B_12]: (r2_hidden(D_16, k2_tarski(D_16, B_12)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.74/2.75  tff(c_151, plain, (![A_78]: (r2_hidden(A_78, k1_tarski(A_78)))), inference(superposition, [status(thm), theory('equality')], [c_145, c_30])).
% 7.74/2.75  tff(c_8314, plain, (![D_730, A_731, C_732, E_733]: (~r2_hidden(D_730, A_731) | k3_mcart_1(C_732, D_730, E_733)!='#skF_5'(A_731) | k1_xboole_0=A_731)), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.74/2.75  tff(c_8322, plain, (![C_732, A_78, E_733]: (k3_mcart_1(C_732, A_78, E_733)!='#skF_5'(k1_tarski(A_78)) | k1_tarski(A_78)=k1_xboole_0)), inference(resolution, [status(thm)], [c_151, c_8314])).
% 7.74/2.75  tff(c_8331, plain, (![C_732, A_78, E_733]: (k3_mcart_1(C_732, A_78, E_733)!=A_78 | k1_tarski(A_78)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8222, c_8322])).
% 7.74/2.75  tff(c_8332, plain, (![C_732, A_78, E_733]: (k3_mcart_1(C_732, A_78, E_733)!=A_78)), inference(negUnitSimplification, [status(thm)], [c_8200, c_8331])).
% 7.74/2.75  tff(c_88, plain, (m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.74/2.75  tff(c_4200, plain, (![A_401, B_402, C_403]: (k4_tarski(k4_tarski(A_401, B_402), C_403)=k3_mcart_1(A_401, B_402, C_403))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.74/2.75  tff(c_84, plain, (![A_61, B_62]: (k2_mcart_1(k4_tarski(A_61, B_62))=B_62)), inference(cnfTransformation, [status(thm)], [f_137])).
% 7.74/2.75  tff(c_64, plain, (![B_35, C_36]: (k2_mcart_1(k4_tarski(B_35, C_36))!=k4_tarski(B_35, C_36))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.74/2.75  tff(c_96, plain, (![B_35, C_36]: (k4_tarski(B_35, C_36)!=C_36)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_64])).
% 7.74/2.75  tff(c_4218, plain, (![A_401, B_402, C_403]: (k3_mcart_1(A_401, B_402, C_403)!=C_403)), inference(superposition, [status(thm), theory('equality')], [c_4200, c_96])).
% 7.74/2.75  tff(c_188, plain, (![D_86, B_87, A_88]: (r2_hidden(D_86, B_87) | ~r2_hidden(D_86, k3_xboole_0(A_88, B_87)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.74/2.75  tff(c_484, plain, (![A_134, B_135]: (r2_hidden('#skF_5'(k3_xboole_0(A_134, B_135)), B_135) | k3_xboole_0(A_134, B_135)=k1_xboole_0)), inference(resolution, [status(thm)], [c_68, c_188])).
% 7.74/2.75  tff(c_520, plain, (![A_134]: (k3_xboole_0(A_134, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_484, c_165])).
% 7.74/2.75  tff(c_194, plain, (![A_89, B_90]: (k4_xboole_0(A_89, k4_xboole_0(A_89, B_90))=k3_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.74/2.75  tff(c_213, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_194])).
% 7.74/2.75  tff(c_540, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_520, c_213])).
% 7.74/2.75  tff(c_651, plain, (![B_143, C_144, A_145]: (~r2_hidden(B_143, C_144) | k4_xboole_0(k2_tarski(A_145, B_143), C_144)!=k2_tarski(A_145, B_143))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.74/2.75  tff(c_655, plain, (![B_143, A_145]: (~r2_hidden(B_143, k2_tarski(A_145, B_143)) | k2_tarski(A_145, B_143)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_540, c_651])).
% 7.74/2.75  tff(c_676, plain, (![A_146, B_147]: (k2_tarski(A_146, B_147)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_655])).
% 7.74/2.75  tff(c_678, plain, (![A_17]: (k1_tarski(A_17)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_44, c_676])).
% 7.74/2.75  tff(c_340, plain, (![D_104, B_105, A_106]: (D_104=B_105 | D_104=A_106 | ~r2_hidden(D_104, k2_tarski(A_106, B_105)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.74/2.75  tff(c_359, plain, (![D_107, A_108]: (D_107=A_108 | D_107=A_108 | ~r2_hidden(D_107, k1_tarski(A_108)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_340])).
% 7.74/2.75  tff(c_367, plain, (![A_108]: ('#skF_5'(k1_tarski(A_108))=A_108 | k1_tarski(A_108)=k1_xboole_0)), inference(resolution, [status(thm)], [c_68, c_359])).
% 7.74/2.75  tff(c_679, plain, (![A_108]: ('#skF_5'(k1_tarski(A_108))=A_108)), inference(negUnitSimplification, [status(thm)], [c_678, c_367])).
% 7.74/2.75  tff(c_681, plain, (![A_149]: ('#skF_5'(k1_tarski(A_149))=A_149)), inference(negUnitSimplification, [status(thm)], [c_678, c_367])).
% 7.74/2.75  tff(c_422, plain, (![C_122, A_123, D_124, E_125]: (~r2_hidden(C_122, A_123) | k3_mcart_1(C_122, D_124, E_125)!='#skF_5'(A_123) | k1_xboole_0=A_123)), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.74/2.75  tff(c_431, plain, (![A_37, D_124, E_125]: (k3_mcart_1('#skF_5'(A_37), D_124, E_125)!='#skF_5'(A_37) | k1_xboole_0=A_37)), inference(resolution, [status(thm)], [c_68, c_422])).
% 7.74/2.75  tff(c_687, plain, (![A_149, D_124, E_125]: (k3_mcart_1(A_149, D_124, E_125)!='#skF_5'(k1_tarski(A_149)) | k1_tarski(A_149)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_681, c_431])).
% 7.74/2.75  tff(c_695, plain, (![A_149, D_124, E_125]: (k3_mcart_1(A_149, D_124, E_125)!=A_149 | k1_tarski(A_149)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_679, c_687])).
% 7.74/2.75  tff(c_696, plain, (![A_149, D_124, E_125]: (k3_mcart_1(A_149, D_124, E_125)!=A_149)), inference(negUnitSimplification, [status(thm)], [c_678, c_695])).
% 7.74/2.75  tff(c_86, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9' | k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9' | k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.74/2.75  tff(c_183, plain, (k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitLeft, [status(thm)], [c_86])).
% 7.74/2.75  tff(c_2143, plain, (![A_297, B_298, C_299, D_300]: (k7_mcart_1(A_297, B_298, C_299, D_300)=k2_mcart_1(D_300) | ~m1_subset_1(D_300, k3_zfmisc_1(A_297, B_298, C_299)) | k1_xboole_0=C_299 | k1_xboole_0=B_298 | k1_xboole_0=A_297)), inference(cnfTransformation, [status(thm)], [f_133])).
% 7.74/2.75  tff(c_2149, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_88, c_2143])).
% 7.74/2.75  tff(c_2152, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')=k2_mcart_1('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_94, c_92, c_90, c_2149])).
% 7.74/2.75  tff(c_3989, plain, (![A_382, B_383, C_384, D_385]: (k3_mcart_1(k5_mcart_1(A_382, B_383, C_384, D_385), k6_mcart_1(A_382, B_383, C_384, D_385), k7_mcart_1(A_382, B_383, C_384, D_385))=D_385 | ~m1_subset_1(D_385, k3_zfmisc_1(A_382, B_383, C_384)) | k1_xboole_0=C_384 | k1_xboole_0=B_383 | k1_xboole_0=A_382)), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.74/2.75  tff(c_4046, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k2_mcart_1('#skF_9'))='#skF_9' | ~m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_2152, c_3989])).
% 7.74/2.75  tff(c_4053, plain, (k3_mcart_1('#skF_9', k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k2_mcart_1('#skF_9'))='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_183, c_4046])).
% 7.74/2.75  tff(c_4055, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_92, c_90, c_696, c_4053])).
% 7.74/2.75  tff(c_4056, plain, (k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9' | k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitRight, [status(thm)], [c_86])).
% 7.74/2.75  tff(c_4153, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitLeft, [status(thm)], [c_4056])).
% 7.74/2.75  tff(c_7819, plain, (![A_677, B_678, C_679, D_680]: (k3_mcart_1(k5_mcart_1(A_677, B_678, C_679, D_680), k6_mcart_1(A_677, B_678, C_679, D_680), k7_mcart_1(A_677, B_678, C_679, D_680))=D_680 | ~m1_subset_1(D_680, k3_zfmisc_1(A_677, B_678, C_679)) | k1_xboole_0=C_679 | k1_xboole_0=B_678 | k1_xboole_0=A_677)), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.74/2.75  tff(c_7876, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9')='#skF_9' | ~m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_4153, c_7819])).
% 7.74/2.75  tff(c_7880, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9')='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_7876])).
% 7.74/2.75  tff(c_7882, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_92, c_90, c_4218, c_7880])).
% 7.74/2.75  tff(c_7883, plain, (k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitRight, [status(thm)], [c_4056])).
% 7.74/2.75  tff(c_9999, plain, (![A_894, B_895, C_896, D_897]: (k7_mcart_1(A_894, B_895, C_896, D_897)=k2_mcart_1(D_897) | ~m1_subset_1(D_897, k3_zfmisc_1(A_894, B_895, C_896)) | k1_xboole_0=C_896 | k1_xboole_0=B_895 | k1_xboole_0=A_894)), inference(cnfTransformation, [status(thm)], [f_133])).
% 7.74/2.75  tff(c_10005, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_88, c_9999])).
% 7.74/2.75  tff(c_10008, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')=k2_mcart_1('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_94, c_92, c_90, c_10005])).
% 7.74/2.75  tff(c_11574, plain, (![A_962, B_963, C_964, D_965]: (k3_mcart_1(k5_mcart_1(A_962, B_963, C_964, D_965), k6_mcart_1(A_962, B_963, C_964, D_965), k7_mcart_1(A_962, B_963, C_964, D_965))=D_965 | ~m1_subset_1(D_965, k3_zfmisc_1(A_962, B_963, C_964)) | k1_xboole_0=C_964 | k1_xboole_0=B_963 | k1_xboole_0=A_962)), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.74/2.75  tff(c_11631, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k2_mcart_1('#skF_9'))='#skF_9' | ~m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_10008, c_11574])).
% 7.74/2.75  tff(c_11638, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9', k2_mcart_1('#skF_9'))='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_7883, c_11631])).
% 7.74/2.75  tff(c_11640, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_92, c_90, c_8332, c_11638])).
% 7.74/2.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.74/2.75  
% 7.74/2.75  Inference rules
% 7.74/2.75  ----------------------
% 7.74/2.75  #Ref     : 0
% 7.74/2.75  #Sup     : 2569
% 7.74/2.75  #Fact    : 8
% 7.74/2.75  #Define  : 0
% 7.74/2.75  #Split   : 2
% 7.74/2.75  #Chain   : 0
% 7.74/2.75  #Close   : 0
% 7.74/2.75  
% 7.74/2.75  Ordering : KBO
% 7.74/2.75  
% 7.74/2.75  Simplification rules
% 7.74/2.75  ----------------------
% 7.74/2.75  #Subsume      : 515
% 7.74/2.75  #Demod        : 992
% 7.74/2.75  #Tautology    : 873
% 7.74/2.75  #SimpNegUnit  : 456
% 7.74/2.75  #BackRed      : 13
% 7.74/2.75  
% 7.74/2.75  #Partial instantiations: 0
% 7.74/2.75  #Strategies tried      : 1
% 7.74/2.75  
% 7.74/2.75  Timing (in seconds)
% 7.74/2.75  ----------------------
% 7.74/2.76  Preprocessing        : 0.37
% 7.74/2.76  Parsing              : 0.19
% 7.74/2.76  CNF conversion       : 0.03
% 7.74/2.76  Main loop            : 1.59
% 7.74/2.76  Inferencing          : 0.53
% 7.74/2.76  Reduction            : 0.53
% 7.74/2.76  Demodulation         : 0.35
% 7.74/2.76  BG Simplification    : 0.07
% 7.74/2.76  Subsumption          : 0.33
% 7.74/2.76  Abstraction          : 0.09
% 7.74/2.76  MUC search           : 0.00
% 7.74/2.76  Cooper               : 0.00
% 7.74/2.76  Total                : 2.00
% 7.74/2.76  Index Insertion      : 0.00
% 7.74/2.76  Index Deletion       : 0.00
% 7.74/2.76  Index Matching       : 0.00
% 7.74/2.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
