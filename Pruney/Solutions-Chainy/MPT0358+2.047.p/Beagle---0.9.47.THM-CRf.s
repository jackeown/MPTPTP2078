%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:06 EST 2020

% Result     : Theorem 4.65s
% Output     : CNFRefutation 4.65s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 400 expanded)
%              Number of leaves         :   33 ( 145 expanded)
%              Depth                    :   15
%              Number of atoms          :  148 ( 760 expanded)
%              Number of equality atoms :   46 ( 209 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_2 > #skF_8 > #skF_3 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_85,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_50,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_82,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_52,plain,(
    ! [A_25] : k1_subset_1(A_25) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_60,plain,
    ( k1_subset_1('#skF_7') != '#skF_8'
    | ~ r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_68,plain,
    ( k1_xboole_0 != '#skF_8'
    | ~ r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_60])).

tff(c_99,plain,(
    ~ r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_56,plain,(
    ! [A_28] : ~ v1_xboole_0(k1_zfmisc_1(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_121,plain,(
    ! [B_44,A_45] :
      ( r2_hidden(B_44,A_45)
      | ~ m1_subset_1(B_44,A_45)
      | v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_32,plain,(
    ! [C_22,A_18] :
      ( r1_tarski(C_22,A_18)
      | ~ r2_hidden(C_22,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_125,plain,(
    ! [B_44,A_18] :
      ( r1_tarski(B_44,A_18)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_18))
      | v1_xboole_0(k1_zfmisc_1(A_18)) ) ),
    inference(resolution,[status(thm)],[c_121,c_32])).

tff(c_129,plain,(
    ! [B_46,A_47] :
      ( r1_tarski(B_46,A_47)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_125])).

tff(c_138,plain,(
    r1_tarski('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_129])).

tff(c_66,plain,
    ( r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_8'))
    | k1_subset_1('#skF_7') = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_67,plain,
    ( r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_66])).

tff(c_100,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_26,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_4'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_101,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_4'(A_12),A_12)
      | A_12 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_26])).

tff(c_182,plain,(
    ! [D_55,A_56,B_57] :
      ( r2_hidden(D_55,A_56)
      | ~ r2_hidden(D_55,k4_xboole_0(A_56,B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1560,plain,(
    ! [A_152,B_153] :
      ( r2_hidden('#skF_4'(k4_xboole_0(A_152,B_153)),A_152)
      | k4_xboole_0(A_152,B_153) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_101,c_182])).

tff(c_171,plain,(
    ! [D_52,B_53,A_54] :
      ( ~ r2_hidden(D_52,B_53)
      | ~ r2_hidden(D_52,k4_xboole_0(A_54,B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_181,plain,(
    ! [A_54,B_53] :
      ( ~ r2_hidden('#skF_4'(k4_xboole_0(A_54,B_53)),B_53)
      | k4_xboole_0(A_54,B_53) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_101,c_171])).

tff(c_1615,plain,(
    ! [A_152] : k4_xboole_0(A_152,A_152) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1560,c_181])).

tff(c_229,plain,(
    ! [A_62,B_63] :
      ( ~ r2_hidden('#skF_1'(A_62,B_63),B_63)
      | r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_242,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_229])).

tff(c_34,plain,(
    ! [C_22,A_18] :
      ( r2_hidden(C_22,k1_zfmisc_1(A_18))
      | ~ r1_tarski(C_22,A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_147,plain,(
    ! [B_48,A_49] :
      ( m1_subset_1(B_48,A_49)
      | ~ r2_hidden(B_48,A_49)
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_156,plain,(
    ! [C_22,A_18] :
      ( m1_subset_1(C_22,k1_zfmisc_1(A_18))
      | v1_xboole_0(k1_zfmisc_1(A_18))
      | ~ r1_tarski(C_22,A_18) ) ),
    inference(resolution,[status(thm)],[c_34,c_147])).

tff(c_161,plain,(
    ! [C_22,A_18] :
      ( m1_subset_1(C_22,k1_zfmisc_1(A_18))
      | ~ r1_tarski(C_22,A_18) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_156])).

tff(c_312,plain,(
    ! [A_72,B_73] :
      ( k4_xboole_0(A_72,B_73) = k3_subset_1(A_72,B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_479,plain,(
    ! [A_82,C_83] :
      ( k4_xboole_0(A_82,C_83) = k3_subset_1(A_82,C_83)
      | ~ r1_tarski(C_83,A_82) ) ),
    inference(resolution,[status(thm)],[c_161,c_312])).

tff(c_490,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k3_subset_1(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_242,c_479])).

tff(c_1631,plain,(
    ! [A_1] : k3_subset_1(A_1,A_1) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1615,c_490])).

tff(c_245,plain,(
    ! [A_64] : r1_tarski(A_64,A_64) ),
    inference(resolution,[status(thm)],[c_6,c_229])).

tff(c_30,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_250,plain,(
    ! [A_65] : k3_xboole_0(A_65,A_65) = A_65 ),
    inference(resolution,[status(thm)],[c_245,c_30])).

tff(c_28,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_256,plain,(
    ! [A_65] : k5_xboole_0(A_65,A_65) = k4_xboole_0(A_65,A_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_28])).

tff(c_142,plain,(
    k3_xboole_0('#skF_8','#skF_7') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_138,c_30])).

tff(c_193,plain,(
    ! [A_58,B_59] : k5_xboole_0(A_58,k3_xboole_0(A_58,B_59)) = k4_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_202,plain,(
    k5_xboole_0('#skF_8','#skF_8') = k4_xboole_0('#skF_8','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_193])).

tff(c_275,plain,(
    k4_xboole_0('#skF_8','#skF_7') = k4_xboole_0('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_202])).

tff(c_515,plain,(
    k4_xboole_0('#skF_8','#skF_7') = k3_subset_1('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_275])).

tff(c_262,plain,(
    ! [C_66,B_67,A_68] :
      ( r2_hidden(C_66,B_67)
      | ~ r2_hidden(C_66,A_68)
      | ~ r1_tarski(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_273,plain,(
    ! [A_12,B_67] :
      ( r2_hidden('#skF_4'(A_12),B_67)
      | ~ r1_tarski(A_12,B_67)
      | A_12 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_101,c_262])).

tff(c_1443,plain,(
    ! [A_144,B_145] :
      ( ~ r2_hidden('#skF_4'(k4_xboole_0(A_144,B_145)),B_145)
      | k4_xboole_0(A_144,B_145) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_101,c_171])).

tff(c_1530,plain,(
    ! [A_148,B_149] :
      ( ~ r1_tarski(k4_xboole_0(A_148,B_149),B_149)
      | k4_xboole_0(A_148,B_149) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_273,c_1443])).

tff(c_1533,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_8','#skF_8'),'#skF_7')
    | k4_xboole_0('#skF_8','#skF_7') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_515,c_1530])).

tff(c_1540,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_8','#skF_8'),'#skF_7')
    | k3_subset_1('#skF_8','#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_515,c_1533])).

tff(c_1545,plain,(
    ~ r1_tarski(k3_subset_1('#skF_8','#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1540])).

tff(c_1660,plain,(
    ~ r1_tarski('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1631,c_1545])).

tff(c_1670,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_1660])).

tff(c_1671,plain,(
    k3_subset_1('#skF_8','#skF_8') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1540])).

tff(c_517,plain,(
    ! [A_85] : k4_xboole_0(A_85,A_85) = k3_subset_1(A_85,A_85) ),
    inference(resolution,[status(thm)],[c_242,c_479])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_529,plain,(
    ! [D_11,A_85] :
      ( ~ r2_hidden(D_11,A_85)
      | ~ r2_hidden(D_11,k3_subset_1(A_85,A_85)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_517,c_10])).

tff(c_1802,plain,(
    ! [D_159] :
      ( ~ r2_hidden(D_159,'#skF_8')
      | ~ r2_hidden(D_159,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1671,c_529])).

tff(c_1936,plain,(
    ! [B_164] :
      ( ~ r2_hidden('#skF_1'('#skF_8',B_164),'#skF_8')
      | r1_tarski('#skF_8',B_164) ) ),
    inference(resolution,[status(thm)],[c_6,c_1802])).

tff(c_1944,plain,(
    ! [B_2] : r1_tarski('#skF_8',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_1936])).

tff(c_1951,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1944,c_99])).

tff(c_1952,plain,(
    r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_1954,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_1952])).

tff(c_1955,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_1956,plain,(
    r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_2171,plain,(
    ! [C_193,B_194,A_195] :
      ( r2_hidden(C_193,B_194)
      | ~ r2_hidden(C_193,A_195)
      | ~ r1_tarski(A_195,B_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2183,plain,(
    ! [A_12,B_194] :
      ( r2_hidden('#skF_4'(A_12),B_194)
      | ~ r1_tarski(A_12,B_194)
      | k1_xboole_0 = A_12 ) ),
    inference(resolution,[status(thm)],[c_26,c_2171])).

tff(c_2212,plain,(
    ! [A_198,B_199] :
      ( k4_xboole_0(A_198,B_199) = k3_subset_1(A_198,B_199)
      | ~ m1_subset_1(B_199,k1_zfmisc_1(A_198)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2232,plain,(
    k4_xboole_0('#skF_7','#skF_8') = k3_subset_1('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_2212])).

tff(c_2264,plain,(
    ! [D_201] :
      ( ~ r2_hidden(D_201,'#skF_8')
      | ~ r2_hidden(D_201,k3_subset_1('#skF_7','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2232,c_10])).

tff(c_3602,plain,(
    ! [A_263] :
      ( ~ r2_hidden('#skF_4'(A_263),'#skF_8')
      | ~ r1_tarski(A_263,k3_subset_1('#skF_7','#skF_8'))
      | k1_xboole_0 = A_263 ) ),
    inference(resolution,[status(thm)],[c_2183,c_2264])).

tff(c_3620,plain,
    ( ~ r1_tarski('#skF_8',k3_subset_1('#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_26,c_3602])).

tff(c_3629,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1956,c_3620])).

tff(c_3631,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1955,c_3629])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:06:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.65/1.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.65/1.80  
% 4.65/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.65/1.80  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_2 > #skF_8 > #skF_3 > #skF_1 > #skF_5
% 4.65/1.80  
% 4.65/1.80  %Foreground sorts:
% 4.65/1.80  
% 4.65/1.80  
% 4.65/1.80  %Background operators:
% 4.65/1.80  
% 4.65/1.80  
% 4.65/1.80  %Foreground operators:
% 4.65/1.80  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.65/1.80  tff('#skF_4', type, '#skF_4': $i > $i).
% 4.65/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.65/1.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.65/1.80  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.65/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.65/1.80  tff('#skF_7', type, '#skF_7': $i).
% 4.65/1.80  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.65/1.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.65/1.80  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.65/1.80  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.65/1.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.65/1.80  tff('#skF_8', type, '#skF_8': $i).
% 4.65/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.65/1.80  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.65/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.65/1.80  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 4.65/1.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.65/1.80  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.65/1.80  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.65/1.80  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.65/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.65/1.80  
% 4.65/1.82  tff(f_78, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 4.65/1.82  tff(f_92, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 4.65/1.82  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.65/1.82  tff(f_85, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.65/1.82  tff(f_76, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 4.65/1.82  tff(f_63, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.65/1.82  tff(f_50, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.65/1.82  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.65/1.82  tff(f_82, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 4.65/1.82  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.65/1.82  tff(f_52, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.65/1.82  tff(c_52, plain, (![A_25]: (k1_subset_1(A_25)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.65/1.82  tff(c_60, plain, (k1_subset_1('#skF_7')!='#skF_8' | ~r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.65/1.82  tff(c_68, plain, (k1_xboole_0!='#skF_8' | ~r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_60])).
% 4.65/1.82  tff(c_99, plain, (~r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_8'))), inference(splitLeft, [status(thm)], [c_68])).
% 4.65/1.82  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.65/1.82  tff(c_58, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.65/1.82  tff(c_56, plain, (![A_28]: (~v1_xboole_0(k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.65/1.82  tff(c_121, plain, (![B_44, A_45]: (r2_hidden(B_44, A_45) | ~m1_subset_1(B_44, A_45) | v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.65/1.82  tff(c_32, plain, (![C_22, A_18]: (r1_tarski(C_22, A_18) | ~r2_hidden(C_22, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.65/1.82  tff(c_125, plain, (![B_44, A_18]: (r1_tarski(B_44, A_18) | ~m1_subset_1(B_44, k1_zfmisc_1(A_18)) | v1_xboole_0(k1_zfmisc_1(A_18)))), inference(resolution, [status(thm)], [c_121, c_32])).
% 4.65/1.82  tff(c_129, plain, (![B_46, A_47]: (r1_tarski(B_46, A_47) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)))), inference(negUnitSimplification, [status(thm)], [c_56, c_125])).
% 4.65/1.82  tff(c_138, plain, (r1_tarski('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_58, c_129])).
% 4.65/1.82  tff(c_66, plain, (r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_8')) | k1_subset_1('#skF_7')='#skF_8'), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.65/1.82  tff(c_67, plain, (r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_8')) | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_66])).
% 4.65/1.82  tff(c_100, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_67])).
% 4.65/1.82  tff(c_26, plain, (![A_12]: (r2_hidden('#skF_4'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.65/1.82  tff(c_101, plain, (![A_12]: (r2_hidden('#skF_4'(A_12), A_12) | A_12='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_26])).
% 4.65/1.82  tff(c_182, plain, (![D_55, A_56, B_57]: (r2_hidden(D_55, A_56) | ~r2_hidden(D_55, k4_xboole_0(A_56, B_57)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.65/1.82  tff(c_1560, plain, (![A_152, B_153]: (r2_hidden('#skF_4'(k4_xboole_0(A_152, B_153)), A_152) | k4_xboole_0(A_152, B_153)='#skF_8')), inference(resolution, [status(thm)], [c_101, c_182])).
% 4.65/1.82  tff(c_171, plain, (![D_52, B_53, A_54]: (~r2_hidden(D_52, B_53) | ~r2_hidden(D_52, k4_xboole_0(A_54, B_53)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.65/1.82  tff(c_181, plain, (![A_54, B_53]: (~r2_hidden('#skF_4'(k4_xboole_0(A_54, B_53)), B_53) | k4_xboole_0(A_54, B_53)='#skF_8')), inference(resolution, [status(thm)], [c_101, c_171])).
% 4.65/1.82  tff(c_1615, plain, (![A_152]: (k4_xboole_0(A_152, A_152)='#skF_8')), inference(resolution, [status(thm)], [c_1560, c_181])).
% 4.65/1.82  tff(c_229, plain, (![A_62, B_63]: (~r2_hidden('#skF_1'(A_62, B_63), B_63) | r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.65/1.82  tff(c_242, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_229])).
% 4.65/1.82  tff(c_34, plain, (![C_22, A_18]: (r2_hidden(C_22, k1_zfmisc_1(A_18)) | ~r1_tarski(C_22, A_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.65/1.82  tff(c_147, plain, (![B_48, A_49]: (m1_subset_1(B_48, A_49) | ~r2_hidden(B_48, A_49) | v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.65/1.82  tff(c_156, plain, (![C_22, A_18]: (m1_subset_1(C_22, k1_zfmisc_1(A_18)) | v1_xboole_0(k1_zfmisc_1(A_18)) | ~r1_tarski(C_22, A_18))), inference(resolution, [status(thm)], [c_34, c_147])).
% 4.65/1.82  tff(c_161, plain, (![C_22, A_18]: (m1_subset_1(C_22, k1_zfmisc_1(A_18)) | ~r1_tarski(C_22, A_18))), inference(negUnitSimplification, [status(thm)], [c_56, c_156])).
% 4.65/1.82  tff(c_312, plain, (![A_72, B_73]: (k4_xboole_0(A_72, B_73)=k3_subset_1(A_72, B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(A_72)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.65/1.82  tff(c_479, plain, (![A_82, C_83]: (k4_xboole_0(A_82, C_83)=k3_subset_1(A_82, C_83) | ~r1_tarski(C_83, A_82))), inference(resolution, [status(thm)], [c_161, c_312])).
% 4.65/1.82  tff(c_490, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k3_subset_1(A_1, A_1))), inference(resolution, [status(thm)], [c_242, c_479])).
% 4.65/1.82  tff(c_1631, plain, (![A_1]: (k3_subset_1(A_1, A_1)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1615, c_490])).
% 4.65/1.82  tff(c_245, plain, (![A_64]: (r1_tarski(A_64, A_64))), inference(resolution, [status(thm)], [c_6, c_229])).
% 4.65/1.82  tff(c_30, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.65/1.82  tff(c_250, plain, (![A_65]: (k3_xboole_0(A_65, A_65)=A_65)), inference(resolution, [status(thm)], [c_245, c_30])).
% 4.65/1.82  tff(c_28, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.65/1.82  tff(c_256, plain, (![A_65]: (k5_xboole_0(A_65, A_65)=k4_xboole_0(A_65, A_65))), inference(superposition, [status(thm), theory('equality')], [c_250, c_28])).
% 4.65/1.82  tff(c_142, plain, (k3_xboole_0('#skF_8', '#skF_7')='#skF_8'), inference(resolution, [status(thm)], [c_138, c_30])).
% 4.65/1.82  tff(c_193, plain, (![A_58, B_59]: (k5_xboole_0(A_58, k3_xboole_0(A_58, B_59))=k4_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.65/1.82  tff(c_202, plain, (k5_xboole_0('#skF_8', '#skF_8')=k4_xboole_0('#skF_8', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_142, c_193])).
% 4.65/1.82  tff(c_275, plain, (k4_xboole_0('#skF_8', '#skF_7')=k4_xboole_0('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_256, c_202])).
% 4.65/1.82  tff(c_515, plain, (k4_xboole_0('#skF_8', '#skF_7')=k3_subset_1('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_490, c_275])).
% 4.65/1.82  tff(c_262, plain, (![C_66, B_67, A_68]: (r2_hidden(C_66, B_67) | ~r2_hidden(C_66, A_68) | ~r1_tarski(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.65/1.82  tff(c_273, plain, (![A_12, B_67]: (r2_hidden('#skF_4'(A_12), B_67) | ~r1_tarski(A_12, B_67) | A_12='#skF_8')), inference(resolution, [status(thm)], [c_101, c_262])).
% 4.65/1.82  tff(c_1443, plain, (![A_144, B_145]: (~r2_hidden('#skF_4'(k4_xboole_0(A_144, B_145)), B_145) | k4_xboole_0(A_144, B_145)='#skF_8')), inference(resolution, [status(thm)], [c_101, c_171])).
% 4.65/1.82  tff(c_1530, plain, (![A_148, B_149]: (~r1_tarski(k4_xboole_0(A_148, B_149), B_149) | k4_xboole_0(A_148, B_149)='#skF_8')), inference(resolution, [status(thm)], [c_273, c_1443])).
% 4.65/1.82  tff(c_1533, plain, (~r1_tarski(k3_subset_1('#skF_8', '#skF_8'), '#skF_7') | k4_xboole_0('#skF_8', '#skF_7')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_515, c_1530])).
% 4.65/1.82  tff(c_1540, plain, (~r1_tarski(k3_subset_1('#skF_8', '#skF_8'), '#skF_7') | k3_subset_1('#skF_8', '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_515, c_1533])).
% 4.65/1.82  tff(c_1545, plain, (~r1_tarski(k3_subset_1('#skF_8', '#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_1540])).
% 4.65/1.82  tff(c_1660, plain, (~r1_tarski('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1631, c_1545])).
% 4.65/1.82  tff(c_1670, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_138, c_1660])).
% 4.65/1.82  tff(c_1671, plain, (k3_subset_1('#skF_8', '#skF_8')='#skF_8'), inference(splitRight, [status(thm)], [c_1540])).
% 4.65/1.82  tff(c_517, plain, (![A_85]: (k4_xboole_0(A_85, A_85)=k3_subset_1(A_85, A_85))), inference(resolution, [status(thm)], [c_242, c_479])).
% 4.65/1.82  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.65/1.82  tff(c_529, plain, (![D_11, A_85]: (~r2_hidden(D_11, A_85) | ~r2_hidden(D_11, k3_subset_1(A_85, A_85)))), inference(superposition, [status(thm), theory('equality')], [c_517, c_10])).
% 4.65/1.82  tff(c_1802, plain, (![D_159]: (~r2_hidden(D_159, '#skF_8') | ~r2_hidden(D_159, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1671, c_529])).
% 4.65/1.82  tff(c_1936, plain, (![B_164]: (~r2_hidden('#skF_1'('#skF_8', B_164), '#skF_8') | r1_tarski('#skF_8', B_164))), inference(resolution, [status(thm)], [c_6, c_1802])).
% 4.65/1.82  tff(c_1944, plain, (![B_2]: (r1_tarski('#skF_8', B_2))), inference(resolution, [status(thm)], [c_6, c_1936])).
% 4.65/1.82  tff(c_1951, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1944, c_99])).
% 4.65/1.82  tff(c_1952, plain, (r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_67])).
% 4.65/1.82  tff(c_1954, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_1952])).
% 4.65/1.82  tff(c_1955, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_68])).
% 4.65/1.82  tff(c_1956, plain, (r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_68])).
% 4.65/1.82  tff(c_2171, plain, (![C_193, B_194, A_195]: (r2_hidden(C_193, B_194) | ~r2_hidden(C_193, A_195) | ~r1_tarski(A_195, B_194))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.65/1.82  tff(c_2183, plain, (![A_12, B_194]: (r2_hidden('#skF_4'(A_12), B_194) | ~r1_tarski(A_12, B_194) | k1_xboole_0=A_12)), inference(resolution, [status(thm)], [c_26, c_2171])).
% 4.65/1.82  tff(c_2212, plain, (![A_198, B_199]: (k4_xboole_0(A_198, B_199)=k3_subset_1(A_198, B_199) | ~m1_subset_1(B_199, k1_zfmisc_1(A_198)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.65/1.82  tff(c_2232, plain, (k4_xboole_0('#skF_7', '#skF_8')=k3_subset_1('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_58, c_2212])).
% 4.65/1.82  tff(c_2264, plain, (![D_201]: (~r2_hidden(D_201, '#skF_8') | ~r2_hidden(D_201, k3_subset_1('#skF_7', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_2232, c_10])).
% 4.65/1.82  tff(c_3602, plain, (![A_263]: (~r2_hidden('#skF_4'(A_263), '#skF_8') | ~r1_tarski(A_263, k3_subset_1('#skF_7', '#skF_8')) | k1_xboole_0=A_263)), inference(resolution, [status(thm)], [c_2183, c_2264])).
% 4.65/1.82  tff(c_3620, plain, (~r1_tarski('#skF_8', k3_subset_1('#skF_7', '#skF_8')) | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_26, c_3602])).
% 4.65/1.82  tff(c_3629, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1956, c_3620])).
% 4.65/1.82  tff(c_3631, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1955, c_3629])).
% 4.65/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.65/1.82  
% 4.65/1.82  Inference rules
% 4.65/1.82  ----------------------
% 4.65/1.82  #Ref     : 0
% 4.65/1.82  #Sup     : 772
% 4.65/1.82  #Fact    : 0
% 4.65/1.82  #Define  : 0
% 4.65/1.82  #Split   : 19
% 4.65/1.82  #Chain   : 0
% 4.65/1.82  #Close   : 0
% 4.65/1.82  
% 4.65/1.82  Ordering : KBO
% 4.65/1.82  
% 4.65/1.82  Simplification rules
% 4.65/1.82  ----------------------
% 4.65/1.82  #Subsume      : 84
% 4.65/1.82  #Demod        : 193
% 4.65/1.82  #Tautology    : 197
% 4.65/1.82  #SimpNegUnit  : 51
% 4.65/1.82  #BackRed      : 58
% 4.65/1.82  
% 4.65/1.82  #Partial instantiations: 0
% 4.65/1.82  #Strategies tried      : 1
% 4.65/1.82  
% 4.65/1.82  Timing (in seconds)
% 4.65/1.82  ----------------------
% 4.65/1.82  Preprocessing        : 0.31
% 4.65/1.82  Parsing              : 0.16
% 4.65/1.82  CNF conversion       : 0.02
% 4.65/1.82  Main loop            : 0.74
% 4.65/1.82  Inferencing          : 0.25
% 4.65/1.82  Reduction            : 0.23
% 4.65/1.82  Demodulation         : 0.15
% 4.65/1.82  BG Simplification    : 0.04
% 4.65/1.82  Subsumption          : 0.15
% 4.65/1.82  Abstraction          : 0.04
% 4.65/1.82  MUC search           : 0.00
% 4.65/1.82  Cooper               : 0.00
% 4.65/1.82  Total                : 1.09
% 4.65/1.82  Index Insertion      : 0.00
% 4.65/1.82  Index Deletion       : 0.00
% 4.65/1.82  Index Matching       : 0.00
% 4.65/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
