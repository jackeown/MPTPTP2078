%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:51 EST 2020

% Result     : Theorem 11.03s
% Output     : CNFRefutation 11.03s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 346 expanded)
%              Number of leaves         :   30 ( 124 expanded)
%              Depth                    :   23
%              Number of atoms          :  146 ( 671 expanded)
%              Number of equality atoms :   33 (  69 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_96,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,C)
            <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_86,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,k4_xboole_0(B,C))
     => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(c_85,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | k4_xboole_0(A_49,B_50) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_52,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_82,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_97,plain,(
    k4_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_85,c_82])).

tff(c_58,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_127,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_58])).

tff(c_368,plain,(
    ! [C_80,B_81,A_82] :
      ( r1_tarski(k4_xboole_0(C_80,B_81),k4_xboole_0(C_80,A_82))
      | ~ r1_tarski(A_82,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_5,B_6,C_7] :
      ( r1_tarski(A_5,B_6)
      | ~ r1_tarski(A_5,k4_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_761,plain,(
    ! [C_98,B_99,A_100] :
      ( r1_tarski(k4_xboole_0(C_98,B_99),C_98)
      | ~ r1_tarski(A_100,B_99) ) ),
    inference(resolution,[status(thm)],[c_368,c_10])).

tff(c_1047,plain,(
    ! [C_106] : r1_tarski(k4_xboole_0(C_106,k3_subset_1('#skF_3','#skF_4')),C_106) ),
    inference(resolution,[status(thm)],[c_127,c_761])).

tff(c_401,plain,(
    ! [C_80,B_81,A_82] :
      ( r1_tarski(k4_xboole_0(C_80,B_81),C_80)
      | ~ r1_tarski(A_82,B_81) ) ),
    inference(resolution,[status(thm)],[c_368,c_10])).

tff(c_1084,plain,(
    ! [C_80,C_106] : r1_tarski(k4_xboole_0(C_80,C_106),C_80) ),
    inference(resolution,[status(thm)],[c_1047,c_401])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_46,plain,(
    ! [A_30] : ~ v1_xboole_0(k1_zfmisc_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_144,plain,(
    ! [B_65,A_66] :
      ( r2_hidden(B_65,A_66)
      | ~ m1_subset_1(B_65,A_66)
      | v1_xboole_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_24,plain,(
    ! [C_25,A_21] :
      ( r1_tarski(C_25,A_21)
      | ~ r2_hidden(C_25,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_151,plain,(
    ! [B_65,A_21] :
      ( r1_tarski(B_65,A_21)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_21))
      | v1_xboole_0(k1_zfmisc_1(A_21)) ) ),
    inference(resolution,[status(thm)],[c_144,c_24])).

tff(c_156,plain,(
    ! [B_67,A_68] :
      ( r1_tarski(B_67,A_68)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_68)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_151])).

tff(c_173,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_156])).

tff(c_819,plain,(
    ! [C_103] : r1_tarski(k4_xboole_0(C_103,'#skF_3'),C_103) ),
    inference(resolution,[status(thm)],[c_173,c_761])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1381,plain,(
    ! [C_117] : k4_xboole_0(k4_xboole_0(C_117,'#skF_3'),C_117) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_819,c_6])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( k1_xboole_0 = A_14
      | ~ r1_tarski(A_14,k4_xboole_0(B_15,A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1443,plain,(
    ! [C_118] :
      ( k1_xboole_0 = C_118
      | ~ r1_tarski(C_118,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1381,c_16])).

tff(c_1469,plain,(
    ! [C_106] : k4_xboole_0(k1_xboole_0,C_106) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1084,c_1443])).

tff(c_1536,plain,(
    ! [C_120] : r1_tarski(k1_xboole_0,k4_xboole_0(C_120,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1381,c_1084])).

tff(c_1627,plain,(
    ! [C_124] : r1_tarski(k1_xboole_0,C_124) ),
    inference(resolution,[status(thm)],[c_1536,c_10])).

tff(c_8,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_xboole_0(A_5,C_7)
      | ~ r1_tarski(A_5,k4_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1756,plain,(
    ! [C_126] : r1_xboole_0(k1_xboole_0,C_126) ),
    inference(resolution,[status(thm)],[c_1627,c_8])).

tff(c_18,plain,(
    ! [B_17,A_16,C_18] :
      ( r1_xboole_0(B_17,k4_xboole_0(A_16,C_18))
      | ~ r1_xboole_0(A_16,k4_xboole_0(B_17,C_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1759,plain,(
    ! [B_17,C_18] : r1_xboole_0(B_17,k4_xboole_0(k1_xboole_0,C_18)) ),
    inference(resolution,[status(thm)],[c_1756,c_18])).

tff(c_1780,plain,(
    ! [B_127] : r1_xboole_0(B_127,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1469,c_1759])).

tff(c_20,plain,(
    ! [A_19,B_20] :
      ( k4_xboole_0(A_19,B_20) = A_19
      | ~ r1_xboole_0(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1786,plain,(
    ! [B_127] : k4_xboole_0(B_127,k1_xboole_0) = B_127 ),
    inference(resolution,[status(thm)],[c_1780,c_20])).

tff(c_1892,plain,(
    ! [B_131] : k4_xboole_0(B_131,k1_xboole_0) = B_131 ),
    inference(resolution,[status(thm)],[c_1780,c_20])).

tff(c_2005,plain,(
    ! [B_133] : r1_tarski(B_133,B_133) ),
    inference(superposition,[status(thm),theory(equality)],[c_1892,c_1084])).

tff(c_2063,plain,(
    ! [B_134] : k4_xboole_0(B_134,B_134) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2005,c_6])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_138,plain,(
    ! [A_62,C_63,B_64] :
      ( r1_xboole_0(A_62,C_63)
      | ~ r1_tarski(A_62,k4_xboole_0(B_64,C_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_143,plain,(
    ! [A_3,C_63,B_64] :
      ( r1_xboole_0(A_3,C_63)
      | k4_xboole_0(A_3,k4_xboole_0(B_64,C_63)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_138])).

tff(c_2072,plain,(
    ! [A_3,B_134] :
      ( r1_xboole_0(A_3,B_134)
      | k4_xboole_0(A_3,k1_xboole_0) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2063,c_143])).

tff(c_2652,plain,(
    ! [A_148,B_149] :
      ( r1_xboole_0(A_148,B_149)
      | k1_xboole_0 != A_148 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1786,c_2072])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2708,plain,(
    ! [B_149] : r1_xboole_0(B_149,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2652,c_2])).

tff(c_201,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_173,c_6])).

tff(c_276,plain,(
    ! [B_73,A_74,C_75] :
      ( r1_xboole_0(B_73,k4_xboole_0(A_74,C_75))
      | ~ r1_xboole_0(A_74,k4_xboole_0(B_73,C_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_280,plain,(
    ! [A_74] :
      ( r1_xboole_0('#skF_4',k4_xboole_0(A_74,'#skF_3'))
      | ~ r1_xboole_0(A_74,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_276])).

tff(c_10916,plain,(
    ! [A_315] : r1_xboole_0('#skF_4',k4_xboole_0(A_315,'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2708,c_280])).

tff(c_11037,plain,(
    ! [A_317] : k4_xboole_0('#skF_4',k4_xboole_0(A_317,'#skF_3')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10916,c_20])).

tff(c_178,plain,(
    ! [A_69,C_70,B_71] :
      ( r1_tarski(k4_xboole_0(A_69,C_70),B_71)
      | ~ r1_tarski(A_69,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_196,plain,(
    ! [A_69,C_70,B_15] :
      ( k4_xboole_0(A_69,C_70) = k1_xboole_0
      | ~ r1_tarski(A_69,k4_xboole_0(B_15,k4_xboole_0(A_69,C_70))) ) ),
    inference(resolution,[status(thm)],[c_178,c_16])).

tff(c_11546,plain,(
    ! [A_324] :
      ( k4_xboole_0(A_324,'#skF_3') = k1_xboole_0
      | ~ r1_tarski(A_324,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11037,c_196])).

tff(c_11613,plain,(
    ! [C_106] : k4_xboole_0(k4_xboole_0('#skF_4',C_106),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1084,c_11546])).

tff(c_478,plain,(
    ! [A_87,B_88] :
      ( k4_xboole_0(A_87,B_88) = k3_subset_1(A_87,B_88)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_495,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_478])).

tff(c_670,plain,(
    ! [A_95] :
      ( r1_xboole_0(A_95,'#skF_4')
      | ~ r1_tarski(A_95,k3_subset_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_495,c_8])).

tff(c_698,plain,(
    r1_xboole_0(k3_subset_1('#skF_3','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_127,c_670])).

tff(c_706,plain,(
    r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_698,c_2])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_494,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_478])).

tff(c_14325,plain,(
    ! [A_361] :
      ( r1_xboole_0('#skF_3',k4_xboole_0(A_361,'#skF_5'))
      | ~ r1_xboole_0(A_361,k3_subset_1('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_18])).

tff(c_14396,plain,(
    r1_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_706,c_14325])).

tff(c_14418,plain,(
    r1_xboole_0(k4_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_14396,c_2])).

tff(c_14422,plain,(
    k4_xboole_0(k4_xboole_0('#skF_4','#skF_5'),'#skF_3') = k4_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_14418,c_20])).

tff(c_14435,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_11613,c_14422])).

tff(c_14437,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_14435])).

tff(c_14438,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_14439,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_14973,plain,(
    ! [A_411,B_412] :
      ( k4_xboole_0(A_411,B_412) = k3_subset_1(A_411,B_412)
      | ~ m1_subset_1(B_412,k1_zfmisc_1(A_411)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_14990,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_14973])).

tff(c_14989,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_14973])).

tff(c_14,plain,(
    ! [C_13,B_12,A_11] :
      ( r1_tarski(k4_xboole_0(C_13,B_12),k4_xboole_0(C_13,A_11))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_29724,plain,(
    ! [A_696] :
      ( r1_tarski(k3_subset_1('#skF_3','#skF_5'),k4_xboole_0('#skF_3',A_696))
      | ~ r1_tarski(A_696,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14989,c_14])).

tff(c_29774,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_14990,c_29724])).

tff(c_29796,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14439,c_29774])).

tff(c_29798,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14438,c_29796])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:45:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.03/4.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.03/4.19  
% 11.03/4.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.03/4.19  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 11.03/4.19  
% 11.03/4.19  %Foreground sorts:
% 11.03/4.19  
% 11.03/4.19  
% 11.03/4.19  %Background operators:
% 11.03/4.19  
% 11.03/4.19  
% 11.03/4.19  %Foreground operators:
% 11.03/4.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.03/4.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.03/4.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.03/4.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.03/4.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.03/4.19  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 11.03/4.19  tff('#skF_5', type, '#skF_5': $i).
% 11.03/4.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.03/4.19  tff('#skF_3', type, '#skF_3': $i).
% 11.03/4.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.03/4.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.03/4.19  tff('#skF_4', type, '#skF_4': $i).
% 11.03/4.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.03/4.19  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.03/4.19  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.03/4.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.03/4.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.03/4.19  
% 11.03/4.21  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 11.03/4.21  tff(f_96, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 11.03/4.21  tff(f_47, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_xboole_1)).
% 11.03/4.21  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 11.03/4.21  tff(f_86, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 11.03/4.21  tff(f_79, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 11.03/4.21  tff(f_66, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 11.03/4.21  tff(f_51, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 11.03/4.21  tff(f_55, axiom, (![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_xboole_1)).
% 11.03/4.21  tff(f_59, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 11.03/4.21  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 11.03/4.21  tff(f_43, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_xboole_1)).
% 11.03/4.21  tff(f_83, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 11.03/4.21  tff(c_85, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | k4_xboole_0(A_49, B_50)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.03/4.21  tff(c_52, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.03/4.21  tff(c_82, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_52])).
% 11.03/4.21  tff(c_97, plain, (k4_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_85, c_82])).
% 11.03/4.21  tff(c_58, plain, (r1_tarski('#skF_4', '#skF_5') | r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.03/4.21  tff(c_127, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_82, c_58])).
% 11.03/4.21  tff(c_368, plain, (![C_80, B_81, A_82]: (r1_tarski(k4_xboole_0(C_80, B_81), k4_xboole_0(C_80, A_82)) | ~r1_tarski(A_82, B_81))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.03/4.21  tff(c_10, plain, (![A_5, B_6, C_7]: (r1_tarski(A_5, B_6) | ~r1_tarski(A_5, k4_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.03/4.21  tff(c_761, plain, (![C_98, B_99, A_100]: (r1_tarski(k4_xboole_0(C_98, B_99), C_98) | ~r1_tarski(A_100, B_99))), inference(resolution, [status(thm)], [c_368, c_10])).
% 11.03/4.21  tff(c_1047, plain, (![C_106]: (r1_tarski(k4_xboole_0(C_106, k3_subset_1('#skF_3', '#skF_4')), C_106))), inference(resolution, [status(thm)], [c_127, c_761])).
% 11.03/4.21  tff(c_401, plain, (![C_80, B_81, A_82]: (r1_tarski(k4_xboole_0(C_80, B_81), C_80) | ~r1_tarski(A_82, B_81))), inference(resolution, [status(thm)], [c_368, c_10])).
% 11.03/4.21  tff(c_1084, plain, (![C_80, C_106]: (r1_tarski(k4_xboole_0(C_80, C_106), C_80))), inference(resolution, [status(thm)], [c_1047, c_401])).
% 11.03/4.21  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.03/4.21  tff(c_46, plain, (![A_30]: (~v1_xboole_0(k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.03/4.21  tff(c_144, plain, (![B_65, A_66]: (r2_hidden(B_65, A_66) | ~m1_subset_1(B_65, A_66) | v1_xboole_0(A_66))), inference(cnfTransformation, [status(thm)], [f_79])).
% 11.03/4.21  tff(c_24, plain, (![C_25, A_21]: (r1_tarski(C_25, A_21) | ~r2_hidden(C_25, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 11.03/4.21  tff(c_151, plain, (![B_65, A_21]: (r1_tarski(B_65, A_21) | ~m1_subset_1(B_65, k1_zfmisc_1(A_21)) | v1_xboole_0(k1_zfmisc_1(A_21)))), inference(resolution, [status(thm)], [c_144, c_24])).
% 11.03/4.21  tff(c_156, plain, (![B_67, A_68]: (r1_tarski(B_67, A_68) | ~m1_subset_1(B_67, k1_zfmisc_1(A_68)))), inference(negUnitSimplification, [status(thm)], [c_46, c_151])).
% 11.03/4.21  tff(c_173, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_156])).
% 11.03/4.21  tff(c_819, plain, (![C_103]: (r1_tarski(k4_xboole_0(C_103, '#skF_3'), C_103))), inference(resolution, [status(thm)], [c_173, c_761])).
% 11.03/4.21  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.03/4.21  tff(c_1381, plain, (![C_117]: (k4_xboole_0(k4_xboole_0(C_117, '#skF_3'), C_117)=k1_xboole_0)), inference(resolution, [status(thm)], [c_819, c_6])).
% 11.03/4.21  tff(c_16, plain, (![A_14, B_15]: (k1_xboole_0=A_14 | ~r1_tarski(A_14, k4_xboole_0(B_15, A_14)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.03/4.21  tff(c_1443, plain, (![C_118]: (k1_xboole_0=C_118 | ~r1_tarski(C_118, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1381, c_16])).
% 11.03/4.21  tff(c_1469, plain, (![C_106]: (k4_xboole_0(k1_xboole_0, C_106)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1084, c_1443])).
% 11.03/4.21  tff(c_1536, plain, (![C_120]: (r1_tarski(k1_xboole_0, k4_xboole_0(C_120, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1381, c_1084])).
% 11.03/4.21  tff(c_1627, plain, (![C_124]: (r1_tarski(k1_xboole_0, C_124))), inference(resolution, [status(thm)], [c_1536, c_10])).
% 11.03/4.21  tff(c_8, plain, (![A_5, C_7, B_6]: (r1_xboole_0(A_5, C_7) | ~r1_tarski(A_5, k4_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.03/4.21  tff(c_1756, plain, (![C_126]: (r1_xboole_0(k1_xboole_0, C_126))), inference(resolution, [status(thm)], [c_1627, c_8])).
% 11.03/4.21  tff(c_18, plain, (![B_17, A_16, C_18]: (r1_xboole_0(B_17, k4_xboole_0(A_16, C_18)) | ~r1_xboole_0(A_16, k4_xboole_0(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.03/4.21  tff(c_1759, plain, (![B_17, C_18]: (r1_xboole_0(B_17, k4_xboole_0(k1_xboole_0, C_18)))), inference(resolution, [status(thm)], [c_1756, c_18])).
% 11.03/4.21  tff(c_1780, plain, (![B_127]: (r1_xboole_0(B_127, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1469, c_1759])).
% 11.03/4.21  tff(c_20, plain, (![A_19, B_20]: (k4_xboole_0(A_19, B_20)=A_19 | ~r1_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.03/4.21  tff(c_1786, plain, (![B_127]: (k4_xboole_0(B_127, k1_xboole_0)=B_127)), inference(resolution, [status(thm)], [c_1780, c_20])).
% 11.03/4.21  tff(c_1892, plain, (![B_131]: (k4_xboole_0(B_131, k1_xboole_0)=B_131)), inference(resolution, [status(thm)], [c_1780, c_20])).
% 11.03/4.21  tff(c_2005, plain, (![B_133]: (r1_tarski(B_133, B_133))), inference(superposition, [status(thm), theory('equality')], [c_1892, c_1084])).
% 11.03/4.21  tff(c_2063, plain, (![B_134]: (k4_xboole_0(B_134, B_134)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2005, c_6])).
% 11.03/4.21  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.03/4.21  tff(c_138, plain, (![A_62, C_63, B_64]: (r1_xboole_0(A_62, C_63) | ~r1_tarski(A_62, k4_xboole_0(B_64, C_63)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.03/4.21  tff(c_143, plain, (![A_3, C_63, B_64]: (r1_xboole_0(A_3, C_63) | k4_xboole_0(A_3, k4_xboole_0(B_64, C_63))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_138])).
% 11.03/4.21  tff(c_2072, plain, (![A_3, B_134]: (r1_xboole_0(A_3, B_134) | k4_xboole_0(A_3, k1_xboole_0)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2063, c_143])).
% 11.03/4.21  tff(c_2652, plain, (![A_148, B_149]: (r1_xboole_0(A_148, B_149) | k1_xboole_0!=A_148)), inference(demodulation, [status(thm), theory('equality')], [c_1786, c_2072])).
% 11.03/4.21  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.03/4.21  tff(c_2708, plain, (![B_149]: (r1_xboole_0(B_149, k1_xboole_0))), inference(resolution, [status(thm)], [c_2652, c_2])).
% 11.03/4.21  tff(c_201, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_173, c_6])).
% 11.03/4.21  tff(c_276, plain, (![B_73, A_74, C_75]: (r1_xboole_0(B_73, k4_xboole_0(A_74, C_75)) | ~r1_xboole_0(A_74, k4_xboole_0(B_73, C_75)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.03/4.21  tff(c_280, plain, (![A_74]: (r1_xboole_0('#skF_4', k4_xboole_0(A_74, '#skF_3')) | ~r1_xboole_0(A_74, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_201, c_276])).
% 11.03/4.21  tff(c_10916, plain, (![A_315]: (r1_xboole_0('#skF_4', k4_xboole_0(A_315, '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2708, c_280])).
% 11.03/4.21  tff(c_11037, plain, (![A_317]: (k4_xboole_0('#skF_4', k4_xboole_0(A_317, '#skF_3'))='#skF_4')), inference(resolution, [status(thm)], [c_10916, c_20])).
% 11.03/4.21  tff(c_178, plain, (![A_69, C_70, B_71]: (r1_tarski(k4_xboole_0(A_69, C_70), B_71) | ~r1_tarski(A_69, B_71))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.03/4.21  tff(c_196, plain, (![A_69, C_70, B_15]: (k4_xboole_0(A_69, C_70)=k1_xboole_0 | ~r1_tarski(A_69, k4_xboole_0(B_15, k4_xboole_0(A_69, C_70))))), inference(resolution, [status(thm)], [c_178, c_16])).
% 11.03/4.21  tff(c_11546, plain, (![A_324]: (k4_xboole_0(A_324, '#skF_3')=k1_xboole_0 | ~r1_tarski(A_324, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_11037, c_196])).
% 11.03/4.21  tff(c_11613, plain, (![C_106]: (k4_xboole_0(k4_xboole_0('#skF_4', C_106), '#skF_3')=k1_xboole_0)), inference(resolution, [status(thm)], [c_1084, c_11546])).
% 11.03/4.21  tff(c_478, plain, (![A_87, B_88]: (k4_xboole_0(A_87, B_88)=k3_subset_1(A_87, B_88) | ~m1_subset_1(B_88, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.03/4.21  tff(c_495, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_478])).
% 11.03/4.21  tff(c_670, plain, (![A_95]: (r1_xboole_0(A_95, '#skF_4') | ~r1_tarski(A_95, k3_subset_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_495, c_8])).
% 11.03/4.21  tff(c_698, plain, (r1_xboole_0(k3_subset_1('#skF_3', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_127, c_670])).
% 11.03/4.21  tff(c_706, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_698, c_2])).
% 11.03/4.21  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.03/4.21  tff(c_494, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_478])).
% 11.03/4.21  tff(c_14325, plain, (![A_361]: (r1_xboole_0('#skF_3', k4_xboole_0(A_361, '#skF_5')) | ~r1_xboole_0(A_361, k3_subset_1('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_494, c_18])).
% 11.03/4.21  tff(c_14396, plain, (r1_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_706, c_14325])).
% 11.03/4.21  tff(c_14418, plain, (r1_xboole_0(k4_xboole_0('#skF_4', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_14396, c_2])).
% 11.03/4.21  tff(c_14422, plain, (k4_xboole_0(k4_xboole_0('#skF_4', '#skF_5'), '#skF_3')=k4_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_14418, c_20])).
% 11.03/4.21  tff(c_14435, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_11613, c_14422])).
% 11.03/4.21  tff(c_14437, plain, $false, inference(negUnitSimplification, [status(thm)], [c_97, c_14435])).
% 11.03/4.21  tff(c_14438, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_52])).
% 11.03/4.21  tff(c_14439, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_52])).
% 11.03/4.21  tff(c_14973, plain, (![A_411, B_412]: (k4_xboole_0(A_411, B_412)=k3_subset_1(A_411, B_412) | ~m1_subset_1(B_412, k1_zfmisc_1(A_411)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.03/4.21  tff(c_14990, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_14973])).
% 11.03/4.21  tff(c_14989, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_14973])).
% 11.03/4.21  tff(c_14, plain, (![C_13, B_12, A_11]: (r1_tarski(k4_xboole_0(C_13, B_12), k4_xboole_0(C_13, A_11)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.03/4.21  tff(c_29724, plain, (![A_696]: (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k4_xboole_0('#skF_3', A_696)) | ~r1_tarski(A_696, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_14989, c_14])).
% 11.03/4.21  tff(c_29774, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_14990, c_29724])).
% 11.03/4.21  tff(c_29796, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14439, c_29774])).
% 11.03/4.21  tff(c_29798, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14438, c_29796])).
% 11.03/4.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.03/4.21  
% 11.03/4.21  Inference rules
% 11.03/4.21  ----------------------
% 11.03/4.21  #Ref     : 0
% 11.03/4.21  #Sup     : 7283
% 11.03/4.21  #Fact    : 0
% 11.03/4.21  #Define  : 0
% 11.03/4.21  #Split   : 15
% 11.03/4.21  #Chain   : 0
% 11.03/4.21  #Close   : 0
% 11.03/4.21  
% 11.03/4.21  Ordering : KBO
% 11.03/4.21  
% 11.03/4.21  Simplification rules
% 11.03/4.21  ----------------------
% 11.03/4.21  #Subsume      : 2009
% 11.03/4.21  #Demod        : 4181
% 11.03/4.21  #Tautology    : 3366
% 11.03/4.21  #SimpNegUnit  : 203
% 11.03/4.21  #BackRed      : 20
% 11.03/4.21  
% 11.03/4.21  #Partial instantiations: 0
% 11.03/4.21  #Strategies tried      : 1
% 11.03/4.21  
% 11.03/4.21  Timing (in seconds)
% 11.03/4.21  ----------------------
% 11.03/4.22  Preprocessing        : 0.37
% 11.03/4.22  Parsing              : 0.18
% 11.03/4.22  CNF conversion       : 0.03
% 11.03/4.22  Main loop            : 3.08
% 11.03/4.22  Inferencing          : 0.77
% 11.03/4.22  Reduction            : 1.23
% 11.03/4.22  Demodulation         : 0.88
% 11.03/4.22  BG Simplification    : 0.09
% 11.03/4.22  Subsumption          : 0.75
% 11.03/4.22  Abstraction          : 0.11
% 11.03/4.22  MUC search           : 0.00
% 11.03/4.22  Cooper               : 0.00
% 11.03/4.22  Total                : 3.49
% 11.03/4.22  Index Insertion      : 0.00
% 11.03/4.22  Index Deletion       : 0.00
% 11.03/4.22  Index Matching       : 0.00
% 11.03/4.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
