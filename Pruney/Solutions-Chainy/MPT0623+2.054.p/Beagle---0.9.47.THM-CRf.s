%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:13 EST 2020

% Result     : Theorem 20.89s
% Output     : CNFRefutation 21.03s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 497 expanded)
%              Number of leaves         :   36 ( 195 expanded)
%              Depth                    :   15
%              Number of atoms          :  213 (1464 expanded)
%              Number of equality atoms :   61 ( 496 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_2 > #skF_17 > #skF_6 > #skF_3 > #skF_13 > #skF_16 > #skF_12 > #skF_8 > #skF_14 > #skF_7 > #skF_1 > #skF_9 > #skF_5 > #skF_15 > #skF_4 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_17',type,(
    '#skF_17': $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_16',type,(
    '#skF_16': $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_14',type,(
    '#skF_14': ( $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_15',type,(
    '#skF_15': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_101,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_83,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_62,plain,
    ( k1_xboole_0 = '#skF_17'
    | k1_xboole_0 != '#skF_16' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_63,plain,(
    k1_xboole_0 != '#skF_16' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_58,plain,(
    ! [A_86,B_87] : v1_relat_1('#skF_15'(A_86,B_87)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_56,plain,(
    ! [A_86,B_87] : v1_funct_1('#skF_15'(A_86,B_87)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_54,plain,(
    ! [A_86,B_87] : k1_relat_1('#skF_15'(A_86,B_87)) = A_86 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_369,plain,(
    ! [A_169,C_170] :
      ( r2_hidden('#skF_14'(A_169,k2_relat_1(A_169),C_170),k1_relat_1(A_169))
      | ~ r2_hidden(C_170,k2_relat_1(A_169))
      | ~ v1_funct_1(A_169)
      | ~ v1_relat_1(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_378,plain,(
    ! [A_86,B_87,C_170] :
      ( r2_hidden('#skF_14'('#skF_15'(A_86,B_87),k2_relat_1('#skF_15'(A_86,B_87)),C_170),A_86)
      | ~ r2_hidden(C_170,k2_relat_1('#skF_15'(A_86,B_87)))
      | ~ v1_funct_1('#skF_15'(A_86,B_87))
      | ~ v1_relat_1('#skF_15'(A_86,B_87)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_369])).

tff(c_383,plain,(
    ! [A_86,B_87,C_170] :
      ( r2_hidden('#skF_14'('#skF_15'(A_86,B_87),k2_relat_1('#skF_15'(A_86,B_87)),C_170),A_86)
      | ~ r2_hidden(C_170,k2_relat_1('#skF_15'(A_86,B_87))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_378])).

tff(c_494,plain,(
    ! [A_180,C_181] :
      ( k1_funct_1(A_180,'#skF_14'(A_180,k2_relat_1(A_180),C_181)) = C_181
      | ~ r2_hidden(C_181,k2_relat_1(A_180))
      | ~ v1_funct_1(A_180)
      | ~ v1_relat_1(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_52,plain,(
    ! [A_86,B_87,D_92] :
      ( k1_funct_1('#skF_15'(A_86,B_87),D_92) = B_87
      | ~ r2_hidden(D_92,A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_504,plain,(
    ! [C_181,B_87,A_86] :
      ( C_181 = B_87
      | ~ r2_hidden('#skF_14'('#skF_15'(A_86,B_87),k2_relat_1('#skF_15'(A_86,B_87)),C_181),A_86)
      | ~ r2_hidden(C_181,k2_relat_1('#skF_15'(A_86,B_87)))
      | ~ v1_funct_1('#skF_15'(A_86,B_87))
      | ~ v1_relat_1('#skF_15'(A_86,B_87)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_52])).

tff(c_12049,plain,(
    ! [C_647,B_648,A_649] :
      ( C_647 = B_648
      | ~ r2_hidden('#skF_14'('#skF_15'(A_649,B_648),k2_relat_1('#skF_15'(A_649,B_648)),C_647),A_649)
      | ~ r2_hidden(C_647,k2_relat_1('#skF_15'(A_649,B_648))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_504])).

tff(c_12060,plain,(
    ! [C_650,B_651,A_652] :
      ( C_650 = B_651
      | ~ r2_hidden(C_650,k2_relat_1('#skF_15'(A_652,B_651))) ) ),
    inference(resolution,[status(thm)],[c_383,c_12049])).

tff(c_13167,plain,(
    ! [A_702,B_703,B_704] :
      ( '#skF_1'(k2_relat_1('#skF_15'(A_702,B_703)),B_704) = B_703
      | r1_tarski(k2_relat_1('#skF_15'(A_702,B_703)),B_704) ) ),
    inference(resolution,[status(thm)],[c_6,c_12060])).

tff(c_60,plain,(
    ! [C_94] :
      ( ~ r1_tarski(k2_relat_1(C_94),'#skF_16')
      | k1_relat_1(C_94) != '#skF_17'
      | ~ v1_funct_1(C_94)
      | ~ v1_relat_1(C_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_13184,plain,(
    ! [A_702,B_703] :
      ( k1_relat_1('#skF_15'(A_702,B_703)) != '#skF_17'
      | ~ v1_funct_1('#skF_15'(A_702,B_703))
      | ~ v1_relat_1('#skF_15'(A_702,B_703))
      | '#skF_1'(k2_relat_1('#skF_15'(A_702,B_703)),'#skF_16') = B_703 ) ),
    inference(resolution,[status(thm)],[c_13167,c_60])).

tff(c_13194,plain,(
    ! [A_705,B_706] :
      ( A_705 != '#skF_17'
      | '#skF_1'(k2_relat_1('#skF_15'(A_705,B_706)),'#skF_16') = B_706 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_13184])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_13242,plain,(
    ! [B_710,A_711] :
      ( ~ r2_hidden(B_710,'#skF_16')
      | r1_tarski(k2_relat_1('#skF_15'(A_711,B_710)),'#skF_16')
      | A_711 != '#skF_17' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13194,c_4])).

tff(c_13254,plain,(
    ! [A_711,B_710] :
      ( k1_relat_1('#skF_15'(A_711,B_710)) != '#skF_17'
      | ~ v1_funct_1('#skF_15'(A_711,B_710))
      | ~ v1_relat_1('#skF_15'(A_711,B_710))
      | ~ r2_hidden(B_710,'#skF_16')
      | A_711 != '#skF_17' ) ),
    inference(resolution,[status(thm)],[c_13242,c_60])).

tff(c_13261,plain,(
    ! [B_710,A_711] :
      ( ~ r2_hidden(B_710,'#skF_16')
      | A_711 != '#skF_17' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_13254])).

tff(c_13262,plain,(
    ! [A_711] : A_711 != '#skF_17' ),
    inference(splitLeft,[status(thm)],[c_13261])).

tff(c_13283,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_13262])).

tff(c_13285,plain,(
    ! [B_715] : ~ r2_hidden(B_715,'#skF_16') ),
    inference(splitRight,[status(thm)],[c_13261])).

tff(c_13365,plain,(
    k1_xboole_0 = '#skF_16' ),
    inference(resolution,[status(thm)],[c_8,c_13285])).

tff(c_13385,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_13365])).

tff(c_13387,plain,(
    k1_xboole_0 = '#skF_16' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_13414,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_16' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13387,c_8])).

tff(c_10,plain,(
    ! [C_23,A_8] :
      ( r2_hidden(k4_tarski(C_23,'#skF_6'(A_8,k1_relat_1(A_8),C_23)),A_8)
      | ~ r2_hidden(C_23,k1_relat_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_13505,plain,(
    ! [A_762,D_763] :
      ( r2_hidden(k1_funct_1(A_762,D_763),k2_relat_1(A_762))
      | ~ r2_hidden(D_763,k1_relat_1(A_762))
      | ~ v1_funct_1(A_762)
      | ~ v1_relat_1(A_762) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_13510,plain,(
    ! [B_87,A_86,D_92] :
      ( r2_hidden(B_87,k2_relat_1('#skF_15'(A_86,B_87)))
      | ~ r2_hidden(D_92,k1_relat_1('#skF_15'(A_86,B_87)))
      | ~ v1_funct_1('#skF_15'(A_86,B_87))
      | ~ v1_relat_1('#skF_15'(A_86,B_87))
      | ~ r2_hidden(D_92,A_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_13505])).

tff(c_13514,plain,(
    ! [B_764,A_765,D_766] :
      ( r2_hidden(B_764,k2_relat_1('#skF_15'(A_765,B_764)))
      | ~ r2_hidden(D_766,A_765) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_13510])).

tff(c_13581,plain,(
    ! [B_775,A_776,C_777] :
      ( r2_hidden(B_775,k2_relat_1('#skF_15'(A_776,B_775)))
      | ~ r2_hidden(C_777,k1_relat_1(A_776)) ) ),
    inference(resolution,[status(thm)],[c_10,c_13514])).

tff(c_13955,plain,(
    ! [B_814,A_815,C_816] :
      ( r2_hidden(B_814,k2_relat_1('#skF_15'(A_815,B_814)))
      | ~ r2_hidden(C_816,k1_relat_1(k1_relat_1(A_815))) ) ),
    inference(resolution,[status(thm)],[c_10,c_13581])).

tff(c_16511,plain,(
    ! [B_994,A_995,C_996] :
      ( r2_hidden(B_994,k2_relat_1('#skF_15'(A_995,B_994)))
      | ~ r2_hidden(C_996,k1_relat_1(k1_relat_1(k1_relat_1(A_995)))) ) ),
    inference(resolution,[status(thm)],[c_10,c_13955])).

tff(c_16565,plain,(
    ! [B_994,A_995] :
      ( r2_hidden(B_994,k2_relat_1('#skF_15'(A_995,B_994)))
      | k1_relat_1(k1_relat_1(k1_relat_1(A_995))) = '#skF_16' ) ),
    inference(resolution,[status(thm)],[c_13414,c_16511])).

tff(c_13843,plain,(
    ! [A_802,C_803] :
      ( r2_hidden('#skF_14'(A_802,k2_relat_1(A_802),C_803),k1_relat_1(A_802))
      | ~ r2_hidden(C_803,k2_relat_1(A_802))
      | ~ v1_funct_1(A_802)
      | ~ v1_relat_1(A_802) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_13852,plain,(
    ! [A_86,B_87,C_803] :
      ( r2_hidden('#skF_14'('#skF_15'(A_86,B_87),k2_relat_1('#skF_15'(A_86,B_87)),C_803),A_86)
      | ~ r2_hidden(C_803,k2_relat_1('#skF_15'(A_86,B_87)))
      | ~ v1_funct_1('#skF_15'(A_86,B_87))
      | ~ v1_relat_1('#skF_15'(A_86,B_87)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_13843])).

tff(c_20488,plain,(
    ! [A_1169,B_1170,C_1171] :
      ( r2_hidden('#skF_14'('#skF_15'(A_1169,B_1170),k2_relat_1('#skF_15'(A_1169,B_1170)),C_1171),A_1169)
      | ~ r2_hidden(C_1171,k2_relat_1('#skF_15'(A_1169,B_1170))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_13852])).

tff(c_13537,plain,(
    ! [B_764,A_8,C_23] :
      ( r2_hidden(B_764,k2_relat_1('#skF_15'(A_8,B_764)))
      | ~ r2_hidden(C_23,k1_relat_1(A_8)) ) ),
    inference(resolution,[status(thm)],[c_10,c_13514])).

tff(c_21366,plain,(
    ! [B_1197,A_1198,C_1199,B_1200] :
      ( r2_hidden(B_1197,k2_relat_1('#skF_15'(A_1198,B_1197)))
      | ~ r2_hidden(C_1199,k2_relat_1('#skF_15'(k1_relat_1(A_1198),B_1200))) ) ),
    inference(resolution,[status(thm)],[c_20488,c_13537])).

tff(c_21594,plain,(
    ! [B_1197,A_1198] :
      ( r2_hidden(B_1197,k2_relat_1('#skF_15'(A_1198,B_1197)))
      | k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(A_1198)))) = '#skF_16' ) ),
    inference(resolution,[status(thm)],[c_16565,c_21366])).

tff(c_13417,plain,(
    ! [A_726,B_727] :
      ( ~ r2_hidden('#skF_1'(A_726,B_727),B_727)
      | r1_tarski(A_726,B_727) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_13422,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_13417])).

tff(c_13486,plain,(
    ! [A_758,C_759] :
      ( r2_hidden(k4_tarski('#skF_10'(A_758,k2_relat_1(A_758),C_759),C_759),A_758)
      | ~ r2_hidden(C_759,k2_relat_1(A_758)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12,plain,(
    ! [C_23,A_8,D_26] :
      ( r2_hidden(C_23,k1_relat_1(A_8))
      | ~ r2_hidden(k4_tarski(C_23,D_26),A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_13497,plain,(
    ! [A_758,C_759] :
      ( r2_hidden('#skF_10'(A_758,k2_relat_1(A_758),C_759),k1_relat_1(A_758))
      | ~ r2_hidden(C_759,k2_relat_1(A_758)) ) ),
    inference(resolution,[status(thm)],[c_13486,c_12])).

tff(c_13784,plain,(
    ! [B_799,A_800,C_801] :
      ( r2_hidden(B_799,k2_relat_1('#skF_15'(k1_relat_1(A_800),B_799)))
      | ~ r2_hidden(C_801,k2_relat_1(A_800)) ) ),
    inference(resolution,[status(thm)],[c_13497,c_13514])).

tff(c_13858,plain,(
    ! [B_804,A_805] :
      ( r2_hidden(B_804,k2_relat_1('#skF_15'(k1_relat_1(A_805),B_804)))
      | k2_relat_1(A_805) = '#skF_16' ) ),
    inference(resolution,[status(thm)],[c_13414,c_13784])).

tff(c_14827,plain,(
    ! [B_889,A_890,B_891] :
      ( r2_hidden(B_889,k2_relat_1('#skF_15'(A_890,B_889)))
      | k2_relat_1('#skF_15'(A_890,B_891)) = '#skF_16' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_13858])).

tff(c_13386,plain,(
    k1_xboole_0 = '#skF_17' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_13393,plain,(
    '#skF_17' = '#skF_16' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13387,c_13386])).

tff(c_13398,plain,(
    ! [C_94] :
      ( ~ r1_tarski(k2_relat_1(C_94),'#skF_16')
      | k1_relat_1(C_94) != '#skF_16'
      | ~ v1_funct_1(C_94)
      | ~ v1_relat_1(C_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13393,c_60])).

tff(c_14986,plain,(
    ! [A_890,B_891,B_889] :
      ( ~ r1_tarski('#skF_16','#skF_16')
      | k1_relat_1('#skF_15'(A_890,B_891)) != '#skF_16'
      | ~ v1_funct_1('#skF_15'(A_890,B_891))
      | ~ v1_relat_1('#skF_15'(A_890,B_891))
      | r2_hidden(B_889,k2_relat_1('#skF_15'(A_890,B_889))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14827,c_13398])).

tff(c_15015,plain,(
    ! [A_890,B_889] :
      ( A_890 != '#skF_16'
      | r2_hidden(B_889,k2_relat_1('#skF_15'(A_890,B_889))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_13422,c_14986])).

tff(c_21632,plain,(
    ! [B_1201,A_1202] :
      ( r2_hidden(B_1201,k2_relat_1('#skF_15'(A_1202,B_1201)))
      | k1_relat_1(A_1202) != '#skF_16' ) ),
    inference(resolution,[status(thm)],[c_15015,c_21366])).

tff(c_20589,plain,(
    ! [B_764,A_8,C_1171,B_1170] :
      ( r2_hidden(B_764,k2_relat_1('#skF_15'(A_8,B_764)))
      | ~ r2_hidden(C_1171,k2_relat_1('#skF_15'(k1_relat_1(A_8),B_1170))) ) ),
    inference(resolution,[status(thm)],[c_20488,c_13537])).

tff(c_21803,plain,(
    ! [B_1206,A_1207] :
      ( r2_hidden(B_1206,k2_relat_1('#skF_15'(A_1207,B_1206)))
      | k1_relat_1(k1_relat_1(A_1207)) != '#skF_16' ) ),
    inference(resolution,[status(thm)],[c_21632,c_20589])).

tff(c_21886,plain,(
    ! [B_1211,A_1212] :
      ( r2_hidden(B_1211,k2_relat_1('#skF_15'(A_1212,B_1211)))
      | k1_relat_1(k1_relat_1(k1_relat_1(A_1212))) != '#skF_16' ) ),
    inference(resolution,[status(thm)],[c_21803,c_20589])).

tff(c_24840,plain,(
    ! [B_1263,A_1264] :
      ( r2_hidden(B_1263,k2_relat_1('#skF_15'(A_1264,B_1263)))
      | k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(A_1264)))) != '#skF_16' ) ),
    inference(resolution,[status(thm)],[c_21886,c_20589])).

tff(c_24861,plain,(
    ! [B_1263,A_1198,B_1197] :
      ( r2_hidden(B_1263,k2_relat_1('#skF_15'(A_1198,B_1263)))
      | r2_hidden(B_1197,k2_relat_1('#skF_15'(A_1198,B_1197))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21594,c_24840])).

tff(c_24874,plain,(
    ! [B_1263,A_1198] : r2_hidden(B_1263,k2_relat_1('#skF_15'(A_1198,B_1263))) ),
    inference(factorization,[status(thm),theory(equality)],[c_24861])).

tff(c_13857,plain,(
    ! [A_86,B_87,C_803] :
      ( r2_hidden('#skF_14'('#skF_15'(A_86,B_87),k2_relat_1('#skF_15'(A_86,B_87)),C_803),A_86)
      | ~ r2_hidden(C_803,k2_relat_1('#skF_15'(A_86,B_87))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_13852])).

tff(c_13715,plain,(
    ! [A_791,C_792] :
      ( k1_funct_1(A_791,'#skF_14'(A_791,k2_relat_1(A_791),C_792)) = C_792
      | ~ r2_hidden(C_792,k2_relat_1(A_791))
      | ~ v1_funct_1(A_791)
      | ~ v1_relat_1(A_791) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_13732,plain,(
    ! [C_792,B_87,A_86] :
      ( C_792 = B_87
      | ~ r2_hidden(C_792,k2_relat_1('#skF_15'(A_86,B_87)))
      | ~ v1_funct_1('#skF_15'(A_86,B_87))
      | ~ v1_relat_1('#skF_15'(A_86,B_87))
      | ~ r2_hidden('#skF_14'('#skF_15'(A_86,B_87),k2_relat_1('#skF_15'(A_86,B_87)),C_792),A_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_13715])).

tff(c_25130,plain,(
    ! [C_1273,B_1274,A_1275] :
      ( C_1273 = B_1274
      | ~ r2_hidden(C_1273,k2_relat_1('#skF_15'(A_1275,B_1274)))
      | ~ r2_hidden('#skF_14'('#skF_15'(A_1275,B_1274),k2_relat_1('#skF_15'(A_1275,B_1274)),C_1273),A_1275) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_13732])).

tff(c_25135,plain,(
    ! [C_1276,B_1277,A_1278] :
      ( C_1276 = B_1277
      | ~ r2_hidden(C_1276,k2_relat_1('#skF_15'(A_1278,B_1277))) ) ),
    inference(resolution,[status(thm)],[c_13857,c_25130])).

tff(c_25424,plain,(
    ! [A_1324,B_1325,B_1326] :
      ( '#skF_1'(k2_relat_1('#skF_15'(A_1324,B_1325)),B_1326) = B_1325
      | r1_tarski(k2_relat_1('#skF_15'(A_1324,B_1325)),B_1326) ) ),
    inference(resolution,[status(thm)],[c_6,c_25135])).

tff(c_25444,plain,(
    ! [A_1324,B_1325] :
      ( k1_relat_1('#skF_15'(A_1324,B_1325)) != '#skF_16'
      | ~ v1_funct_1('#skF_15'(A_1324,B_1325))
      | ~ v1_relat_1('#skF_15'(A_1324,B_1325))
      | '#skF_1'(k2_relat_1('#skF_15'(A_1324,B_1325)),'#skF_16') = B_1325 ) ),
    inference(resolution,[status(thm)],[c_25424,c_13398])).

tff(c_25455,plain,(
    ! [A_1327,B_1328] :
      ( A_1327 != '#skF_16'
      | '#skF_1'(k2_relat_1('#skF_15'(A_1327,B_1328)),'#skF_16') = B_1328 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_25444])).

tff(c_25503,plain,(
    ! [B_1332,A_1333] :
      ( ~ r2_hidden(B_1332,'#skF_16')
      | r1_tarski(k2_relat_1('#skF_15'(A_1333,B_1332)),'#skF_16')
      | A_1333 != '#skF_16' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25455,c_4])).

tff(c_25515,plain,(
    ! [A_1333,B_1332] :
      ( k1_relat_1('#skF_15'(A_1333,B_1332)) != '#skF_16'
      | ~ v1_funct_1('#skF_15'(A_1333,B_1332))
      | ~ v1_relat_1('#skF_15'(A_1333,B_1332))
      | ~ r2_hidden(B_1332,'#skF_16')
      | A_1333 != '#skF_16' ) ),
    inference(resolution,[status(thm)],[c_25503,c_13398])).

tff(c_25522,plain,(
    ! [B_1332,A_1333] :
      ( ~ r2_hidden(B_1332,'#skF_16')
      | A_1333 != '#skF_16' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_25515])).

tff(c_25523,plain,(
    ! [A_1333] : A_1333 != '#skF_16' ),
    inference(splitLeft,[status(thm)],[c_25522])).

tff(c_25548,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25523,c_13393])).

tff(c_25550,plain,(
    ! [B_1337] : ~ r2_hidden(B_1337,'#skF_16') ),
    inference(splitRight,[status(thm)],[c_25522])).

tff(c_26094,plain,(
    ! [C_1350,B_1351] : ~ r2_hidden(C_1350,k2_relat_1('#skF_15'('#skF_16',B_1351))) ),
    inference(resolution,[status(thm)],[c_13857,c_25550])).

tff(c_26215,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_24874,c_26094])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:50:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.89/8.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.96/8.71  
% 20.96/8.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.96/8.71  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_2 > #skF_17 > #skF_6 > #skF_3 > #skF_13 > #skF_16 > #skF_12 > #skF_8 > #skF_14 > #skF_7 > #skF_1 > #skF_9 > #skF_5 > #skF_15 > #skF_4 > #skF_10
% 20.96/8.71  
% 20.96/8.71  %Foreground sorts:
% 20.96/8.71  
% 20.96/8.71  
% 20.96/8.71  %Background operators:
% 20.96/8.71  
% 20.96/8.71  
% 20.96/8.71  %Foreground operators:
% 20.96/8.71  tff('#skF_11', type, '#skF_11': ($i * $i) > $i).
% 20.96/8.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 20.96/8.71  tff('#skF_2', type, '#skF_2': $i > $i).
% 20.96/8.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.96/8.71  tff('#skF_17', type, '#skF_17': $i).
% 20.96/8.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 20.96/8.71  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 20.96/8.71  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 20.96/8.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 20.96/8.71  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 20.96/8.71  tff('#skF_13', type, '#skF_13': ($i * $i) > $i).
% 20.96/8.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.96/8.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 20.96/8.71  tff('#skF_16', type, '#skF_16': $i).
% 20.96/8.71  tff('#skF_12', type, '#skF_12': ($i * $i) > $i).
% 20.96/8.71  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 20.96/8.71  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 20.96/8.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.96/8.71  tff('#skF_14', type, '#skF_14': ($i * $i * $i) > $i).
% 20.96/8.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 20.96/8.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.96/8.71  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 20.96/8.71  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 20.96/8.71  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 20.96/8.71  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 20.96/8.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 20.96/8.71  tff('#skF_15', type, '#skF_15': ($i * $i) > $i).
% 20.96/8.71  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 20.96/8.71  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 20.96/8.71  
% 21.03/8.73  tff(f_101, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 21.03/8.73  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 21.03/8.73  tff(f_83, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 21.03/8.73  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 21.03/8.73  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 21.03/8.73  tff(f_48, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 21.03/8.73  tff(f_56, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 21.03/8.73  tff(c_62, plain, (k1_xboole_0='#skF_17' | k1_xboole_0!='#skF_16'), inference(cnfTransformation, [status(thm)], [f_101])).
% 21.03/8.73  tff(c_63, plain, (k1_xboole_0!='#skF_16'), inference(splitLeft, [status(thm)], [c_62])).
% 21.03/8.73  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 21.03/8.73  tff(c_58, plain, (![A_86, B_87]: (v1_relat_1('#skF_15'(A_86, B_87)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 21.03/8.73  tff(c_56, plain, (![A_86, B_87]: (v1_funct_1('#skF_15'(A_86, B_87)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 21.03/8.73  tff(c_54, plain, (![A_86, B_87]: (k1_relat_1('#skF_15'(A_86, B_87))=A_86)), inference(cnfTransformation, [status(thm)], [f_83])).
% 21.03/8.73  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 21.03/8.73  tff(c_369, plain, (![A_169, C_170]: (r2_hidden('#skF_14'(A_169, k2_relat_1(A_169), C_170), k1_relat_1(A_169)) | ~r2_hidden(C_170, k2_relat_1(A_169)) | ~v1_funct_1(A_169) | ~v1_relat_1(A_169))), inference(cnfTransformation, [status(thm)], [f_71])).
% 21.03/8.73  tff(c_378, plain, (![A_86, B_87, C_170]: (r2_hidden('#skF_14'('#skF_15'(A_86, B_87), k2_relat_1('#skF_15'(A_86, B_87)), C_170), A_86) | ~r2_hidden(C_170, k2_relat_1('#skF_15'(A_86, B_87))) | ~v1_funct_1('#skF_15'(A_86, B_87)) | ~v1_relat_1('#skF_15'(A_86, B_87)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_369])).
% 21.03/8.73  tff(c_383, plain, (![A_86, B_87, C_170]: (r2_hidden('#skF_14'('#skF_15'(A_86, B_87), k2_relat_1('#skF_15'(A_86, B_87)), C_170), A_86) | ~r2_hidden(C_170, k2_relat_1('#skF_15'(A_86, B_87))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_378])).
% 21.03/8.73  tff(c_494, plain, (![A_180, C_181]: (k1_funct_1(A_180, '#skF_14'(A_180, k2_relat_1(A_180), C_181))=C_181 | ~r2_hidden(C_181, k2_relat_1(A_180)) | ~v1_funct_1(A_180) | ~v1_relat_1(A_180))), inference(cnfTransformation, [status(thm)], [f_71])).
% 21.03/8.73  tff(c_52, plain, (![A_86, B_87, D_92]: (k1_funct_1('#skF_15'(A_86, B_87), D_92)=B_87 | ~r2_hidden(D_92, A_86))), inference(cnfTransformation, [status(thm)], [f_83])).
% 21.03/8.73  tff(c_504, plain, (![C_181, B_87, A_86]: (C_181=B_87 | ~r2_hidden('#skF_14'('#skF_15'(A_86, B_87), k2_relat_1('#skF_15'(A_86, B_87)), C_181), A_86) | ~r2_hidden(C_181, k2_relat_1('#skF_15'(A_86, B_87))) | ~v1_funct_1('#skF_15'(A_86, B_87)) | ~v1_relat_1('#skF_15'(A_86, B_87)))), inference(superposition, [status(thm), theory('equality')], [c_494, c_52])).
% 21.03/8.73  tff(c_12049, plain, (![C_647, B_648, A_649]: (C_647=B_648 | ~r2_hidden('#skF_14'('#skF_15'(A_649, B_648), k2_relat_1('#skF_15'(A_649, B_648)), C_647), A_649) | ~r2_hidden(C_647, k2_relat_1('#skF_15'(A_649, B_648))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_504])).
% 21.03/8.73  tff(c_12060, plain, (![C_650, B_651, A_652]: (C_650=B_651 | ~r2_hidden(C_650, k2_relat_1('#skF_15'(A_652, B_651))))), inference(resolution, [status(thm)], [c_383, c_12049])).
% 21.03/8.73  tff(c_13167, plain, (![A_702, B_703, B_704]: ('#skF_1'(k2_relat_1('#skF_15'(A_702, B_703)), B_704)=B_703 | r1_tarski(k2_relat_1('#skF_15'(A_702, B_703)), B_704))), inference(resolution, [status(thm)], [c_6, c_12060])).
% 21.03/8.73  tff(c_60, plain, (![C_94]: (~r1_tarski(k2_relat_1(C_94), '#skF_16') | k1_relat_1(C_94)!='#skF_17' | ~v1_funct_1(C_94) | ~v1_relat_1(C_94))), inference(cnfTransformation, [status(thm)], [f_101])).
% 21.03/8.73  tff(c_13184, plain, (![A_702, B_703]: (k1_relat_1('#skF_15'(A_702, B_703))!='#skF_17' | ~v1_funct_1('#skF_15'(A_702, B_703)) | ~v1_relat_1('#skF_15'(A_702, B_703)) | '#skF_1'(k2_relat_1('#skF_15'(A_702, B_703)), '#skF_16')=B_703)), inference(resolution, [status(thm)], [c_13167, c_60])).
% 21.03/8.73  tff(c_13194, plain, (![A_705, B_706]: (A_705!='#skF_17' | '#skF_1'(k2_relat_1('#skF_15'(A_705, B_706)), '#skF_16')=B_706)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_13184])).
% 21.03/8.73  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 21.03/8.73  tff(c_13242, plain, (![B_710, A_711]: (~r2_hidden(B_710, '#skF_16') | r1_tarski(k2_relat_1('#skF_15'(A_711, B_710)), '#skF_16') | A_711!='#skF_17')), inference(superposition, [status(thm), theory('equality')], [c_13194, c_4])).
% 21.03/8.73  tff(c_13254, plain, (![A_711, B_710]: (k1_relat_1('#skF_15'(A_711, B_710))!='#skF_17' | ~v1_funct_1('#skF_15'(A_711, B_710)) | ~v1_relat_1('#skF_15'(A_711, B_710)) | ~r2_hidden(B_710, '#skF_16') | A_711!='#skF_17')), inference(resolution, [status(thm)], [c_13242, c_60])).
% 21.03/8.73  tff(c_13261, plain, (![B_710, A_711]: (~r2_hidden(B_710, '#skF_16') | A_711!='#skF_17')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_13254])).
% 21.03/8.73  tff(c_13262, plain, (![A_711]: (A_711!='#skF_17')), inference(splitLeft, [status(thm)], [c_13261])).
% 21.03/8.73  tff(c_13283, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_13262])).
% 21.03/8.73  tff(c_13285, plain, (![B_715]: (~r2_hidden(B_715, '#skF_16'))), inference(splitRight, [status(thm)], [c_13261])).
% 21.03/8.73  tff(c_13365, plain, (k1_xboole_0='#skF_16'), inference(resolution, [status(thm)], [c_8, c_13285])).
% 21.03/8.73  tff(c_13385, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_13365])).
% 21.03/8.73  tff(c_13387, plain, (k1_xboole_0='#skF_16'), inference(splitRight, [status(thm)], [c_62])).
% 21.03/8.73  tff(c_13414, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_16')), inference(demodulation, [status(thm), theory('equality')], [c_13387, c_8])).
% 21.03/8.73  tff(c_10, plain, (![C_23, A_8]: (r2_hidden(k4_tarski(C_23, '#skF_6'(A_8, k1_relat_1(A_8), C_23)), A_8) | ~r2_hidden(C_23, k1_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 21.03/8.73  tff(c_13505, plain, (![A_762, D_763]: (r2_hidden(k1_funct_1(A_762, D_763), k2_relat_1(A_762)) | ~r2_hidden(D_763, k1_relat_1(A_762)) | ~v1_funct_1(A_762) | ~v1_relat_1(A_762))), inference(cnfTransformation, [status(thm)], [f_71])).
% 21.03/8.73  tff(c_13510, plain, (![B_87, A_86, D_92]: (r2_hidden(B_87, k2_relat_1('#skF_15'(A_86, B_87))) | ~r2_hidden(D_92, k1_relat_1('#skF_15'(A_86, B_87))) | ~v1_funct_1('#skF_15'(A_86, B_87)) | ~v1_relat_1('#skF_15'(A_86, B_87)) | ~r2_hidden(D_92, A_86))), inference(superposition, [status(thm), theory('equality')], [c_52, c_13505])).
% 21.03/8.73  tff(c_13514, plain, (![B_764, A_765, D_766]: (r2_hidden(B_764, k2_relat_1('#skF_15'(A_765, B_764))) | ~r2_hidden(D_766, A_765))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_13510])).
% 21.03/8.73  tff(c_13581, plain, (![B_775, A_776, C_777]: (r2_hidden(B_775, k2_relat_1('#skF_15'(A_776, B_775))) | ~r2_hidden(C_777, k1_relat_1(A_776)))), inference(resolution, [status(thm)], [c_10, c_13514])).
% 21.03/8.73  tff(c_13955, plain, (![B_814, A_815, C_816]: (r2_hidden(B_814, k2_relat_1('#skF_15'(A_815, B_814))) | ~r2_hidden(C_816, k1_relat_1(k1_relat_1(A_815))))), inference(resolution, [status(thm)], [c_10, c_13581])).
% 21.03/8.73  tff(c_16511, plain, (![B_994, A_995, C_996]: (r2_hidden(B_994, k2_relat_1('#skF_15'(A_995, B_994))) | ~r2_hidden(C_996, k1_relat_1(k1_relat_1(k1_relat_1(A_995)))))), inference(resolution, [status(thm)], [c_10, c_13955])).
% 21.03/8.73  tff(c_16565, plain, (![B_994, A_995]: (r2_hidden(B_994, k2_relat_1('#skF_15'(A_995, B_994))) | k1_relat_1(k1_relat_1(k1_relat_1(A_995)))='#skF_16')), inference(resolution, [status(thm)], [c_13414, c_16511])).
% 21.03/8.73  tff(c_13843, plain, (![A_802, C_803]: (r2_hidden('#skF_14'(A_802, k2_relat_1(A_802), C_803), k1_relat_1(A_802)) | ~r2_hidden(C_803, k2_relat_1(A_802)) | ~v1_funct_1(A_802) | ~v1_relat_1(A_802))), inference(cnfTransformation, [status(thm)], [f_71])).
% 21.03/8.73  tff(c_13852, plain, (![A_86, B_87, C_803]: (r2_hidden('#skF_14'('#skF_15'(A_86, B_87), k2_relat_1('#skF_15'(A_86, B_87)), C_803), A_86) | ~r2_hidden(C_803, k2_relat_1('#skF_15'(A_86, B_87))) | ~v1_funct_1('#skF_15'(A_86, B_87)) | ~v1_relat_1('#skF_15'(A_86, B_87)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_13843])).
% 21.03/8.73  tff(c_20488, plain, (![A_1169, B_1170, C_1171]: (r2_hidden('#skF_14'('#skF_15'(A_1169, B_1170), k2_relat_1('#skF_15'(A_1169, B_1170)), C_1171), A_1169) | ~r2_hidden(C_1171, k2_relat_1('#skF_15'(A_1169, B_1170))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_13852])).
% 21.03/8.73  tff(c_13537, plain, (![B_764, A_8, C_23]: (r2_hidden(B_764, k2_relat_1('#skF_15'(A_8, B_764))) | ~r2_hidden(C_23, k1_relat_1(A_8)))), inference(resolution, [status(thm)], [c_10, c_13514])).
% 21.03/8.73  tff(c_21366, plain, (![B_1197, A_1198, C_1199, B_1200]: (r2_hidden(B_1197, k2_relat_1('#skF_15'(A_1198, B_1197))) | ~r2_hidden(C_1199, k2_relat_1('#skF_15'(k1_relat_1(A_1198), B_1200))))), inference(resolution, [status(thm)], [c_20488, c_13537])).
% 21.03/8.73  tff(c_21594, plain, (![B_1197, A_1198]: (r2_hidden(B_1197, k2_relat_1('#skF_15'(A_1198, B_1197))) | k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(A_1198))))='#skF_16')), inference(resolution, [status(thm)], [c_16565, c_21366])).
% 21.03/8.73  tff(c_13417, plain, (![A_726, B_727]: (~r2_hidden('#skF_1'(A_726, B_727), B_727) | r1_tarski(A_726, B_727))), inference(cnfTransformation, [status(thm)], [f_32])).
% 21.03/8.73  tff(c_13422, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_13417])).
% 21.03/8.73  tff(c_13486, plain, (![A_758, C_759]: (r2_hidden(k4_tarski('#skF_10'(A_758, k2_relat_1(A_758), C_759), C_759), A_758) | ~r2_hidden(C_759, k2_relat_1(A_758)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 21.03/8.73  tff(c_12, plain, (![C_23, A_8, D_26]: (r2_hidden(C_23, k1_relat_1(A_8)) | ~r2_hidden(k4_tarski(C_23, D_26), A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 21.03/8.73  tff(c_13497, plain, (![A_758, C_759]: (r2_hidden('#skF_10'(A_758, k2_relat_1(A_758), C_759), k1_relat_1(A_758)) | ~r2_hidden(C_759, k2_relat_1(A_758)))), inference(resolution, [status(thm)], [c_13486, c_12])).
% 21.03/8.73  tff(c_13784, plain, (![B_799, A_800, C_801]: (r2_hidden(B_799, k2_relat_1('#skF_15'(k1_relat_1(A_800), B_799))) | ~r2_hidden(C_801, k2_relat_1(A_800)))), inference(resolution, [status(thm)], [c_13497, c_13514])).
% 21.03/8.73  tff(c_13858, plain, (![B_804, A_805]: (r2_hidden(B_804, k2_relat_1('#skF_15'(k1_relat_1(A_805), B_804))) | k2_relat_1(A_805)='#skF_16')), inference(resolution, [status(thm)], [c_13414, c_13784])).
% 21.03/8.73  tff(c_14827, plain, (![B_889, A_890, B_891]: (r2_hidden(B_889, k2_relat_1('#skF_15'(A_890, B_889))) | k2_relat_1('#skF_15'(A_890, B_891))='#skF_16')), inference(superposition, [status(thm), theory('equality')], [c_54, c_13858])).
% 21.03/8.73  tff(c_13386, plain, (k1_xboole_0='#skF_17'), inference(splitRight, [status(thm)], [c_62])).
% 21.03/8.73  tff(c_13393, plain, ('#skF_17'='#skF_16'), inference(demodulation, [status(thm), theory('equality')], [c_13387, c_13386])).
% 21.03/8.73  tff(c_13398, plain, (![C_94]: (~r1_tarski(k2_relat_1(C_94), '#skF_16') | k1_relat_1(C_94)!='#skF_16' | ~v1_funct_1(C_94) | ~v1_relat_1(C_94))), inference(demodulation, [status(thm), theory('equality')], [c_13393, c_60])).
% 21.03/8.73  tff(c_14986, plain, (![A_890, B_891, B_889]: (~r1_tarski('#skF_16', '#skF_16') | k1_relat_1('#skF_15'(A_890, B_891))!='#skF_16' | ~v1_funct_1('#skF_15'(A_890, B_891)) | ~v1_relat_1('#skF_15'(A_890, B_891)) | r2_hidden(B_889, k2_relat_1('#skF_15'(A_890, B_889))))), inference(superposition, [status(thm), theory('equality')], [c_14827, c_13398])).
% 21.03/8.73  tff(c_15015, plain, (![A_890, B_889]: (A_890!='#skF_16' | r2_hidden(B_889, k2_relat_1('#skF_15'(A_890, B_889))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_13422, c_14986])).
% 21.03/8.73  tff(c_21632, plain, (![B_1201, A_1202]: (r2_hidden(B_1201, k2_relat_1('#skF_15'(A_1202, B_1201))) | k1_relat_1(A_1202)!='#skF_16')), inference(resolution, [status(thm)], [c_15015, c_21366])).
% 21.03/8.73  tff(c_20589, plain, (![B_764, A_8, C_1171, B_1170]: (r2_hidden(B_764, k2_relat_1('#skF_15'(A_8, B_764))) | ~r2_hidden(C_1171, k2_relat_1('#skF_15'(k1_relat_1(A_8), B_1170))))), inference(resolution, [status(thm)], [c_20488, c_13537])).
% 21.03/8.73  tff(c_21803, plain, (![B_1206, A_1207]: (r2_hidden(B_1206, k2_relat_1('#skF_15'(A_1207, B_1206))) | k1_relat_1(k1_relat_1(A_1207))!='#skF_16')), inference(resolution, [status(thm)], [c_21632, c_20589])).
% 21.03/8.73  tff(c_21886, plain, (![B_1211, A_1212]: (r2_hidden(B_1211, k2_relat_1('#skF_15'(A_1212, B_1211))) | k1_relat_1(k1_relat_1(k1_relat_1(A_1212)))!='#skF_16')), inference(resolution, [status(thm)], [c_21803, c_20589])).
% 21.03/8.73  tff(c_24840, plain, (![B_1263, A_1264]: (r2_hidden(B_1263, k2_relat_1('#skF_15'(A_1264, B_1263))) | k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(A_1264))))!='#skF_16')), inference(resolution, [status(thm)], [c_21886, c_20589])).
% 21.03/8.73  tff(c_24861, plain, (![B_1263, A_1198, B_1197]: (r2_hidden(B_1263, k2_relat_1('#skF_15'(A_1198, B_1263))) | r2_hidden(B_1197, k2_relat_1('#skF_15'(A_1198, B_1197))))), inference(superposition, [status(thm), theory('equality')], [c_21594, c_24840])).
% 21.03/8.73  tff(c_24874, plain, (![B_1263, A_1198]: (r2_hidden(B_1263, k2_relat_1('#skF_15'(A_1198, B_1263))))), inference(factorization, [status(thm), theory('equality')], [c_24861])).
% 21.03/8.73  tff(c_13857, plain, (![A_86, B_87, C_803]: (r2_hidden('#skF_14'('#skF_15'(A_86, B_87), k2_relat_1('#skF_15'(A_86, B_87)), C_803), A_86) | ~r2_hidden(C_803, k2_relat_1('#skF_15'(A_86, B_87))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_13852])).
% 21.03/8.73  tff(c_13715, plain, (![A_791, C_792]: (k1_funct_1(A_791, '#skF_14'(A_791, k2_relat_1(A_791), C_792))=C_792 | ~r2_hidden(C_792, k2_relat_1(A_791)) | ~v1_funct_1(A_791) | ~v1_relat_1(A_791))), inference(cnfTransformation, [status(thm)], [f_71])).
% 21.03/8.73  tff(c_13732, plain, (![C_792, B_87, A_86]: (C_792=B_87 | ~r2_hidden(C_792, k2_relat_1('#skF_15'(A_86, B_87))) | ~v1_funct_1('#skF_15'(A_86, B_87)) | ~v1_relat_1('#skF_15'(A_86, B_87)) | ~r2_hidden('#skF_14'('#skF_15'(A_86, B_87), k2_relat_1('#skF_15'(A_86, B_87)), C_792), A_86))), inference(superposition, [status(thm), theory('equality')], [c_52, c_13715])).
% 21.03/8.73  tff(c_25130, plain, (![C_1273, B_1274, A_1275]: (C_1273=B_1274 | ~r2_hidden(C_1273, k2_relat_1('#skF_15'(A_1275, B_1274))) | ~r2_hidden('#skF_14'('#skF_15'(A_1275, B_1274), k2_relat_1('#skF_15'(A_1275, B_1274)), C_1273), A_1275))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_13732])).
% 21.03/8.73  tff(c_25135, plain, (![C_1276, B_1277, A_1278]: (C_1276=B_1277 | ~r2_hidden(C_1276, k2_relat_1('#skF_15'(A_1278, B_1277))))), inference(resolution, [status(thm)], [c_13857, c_25130])).
% 21.03/8.73  tff(c_25424, plain, (![A_1324, B_1325, B_1326]: ('#skF_1'(k2_relat_1('#skF_15'(A_1324, B_1325)), B_1326)=B_1325 | r1_tarski(k2_relat_1('#skF_15'(A_1324, B_1325)), B_1326))), inference(resolution, [status(thm)], [c_6, c_25135])).
% 21.03/8.73  tff(c_25444, plain, (![A_1324, B_1325]: (k1_relat_1('#skF_15'(A_1324, B_1325))!='#skF_16' | ~v1_funct_1('#skF_15'(A_1324, B_1325)) | ~v1_relat_1('#skF_15'(A_1324, B_1325)) | '#skF_1'(k2_relat_1('#skF_15'(A_1324, B_1325)), '#skF_16')=B_1325)), inference(resolution, [status(thm)], [c_25424, c_13398])).
% 21.03/8.73  tff(c_25455, plain, (![A_1327, B_1328]: (A_1327!='#skF_16' | '#skF_1'(k2_relat_1('#skF_15'(A_1327, B_1328)), '#skF_16')=B_1328)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_25444])).
% 21.03/8.73  tff(c_25503, plain, (![B_1332, A_1333]: (~r2_hidden(B_1332, '#skF_16') | r1_tarski(k2_relat_1('#skF_15'(A_1333, B_1332)), '#skF_16') | A_1333!='#skF_16')), inference(superposition, [status(thm), theory('equality')], [c_25455, c_4])).
% 21.03/8.73  tff(c_25515, plain, (![A_1333, B_1332]: (k1_relat_1('#skF_15'(A_1333, B_1332))!='#skF_16' | ~v1_funct_1('#skF_15'(A_1333, B_1332)) | ~v1_relat_1('#skF_15'(A_1333, B_1332)) | ~r2_hidden(B_1332, '#skF_16') | A_1333!='#skF_16')), inference(resolution, [status(thm)], [c_25503, c_13398])).
% 21.03/8.73  tff(c_25522, plain, (![B_1332, A_1333]: (~r2_hidden(B_1332, '#skF_16') | A_1333!='#skF_16')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_25515])).
% 21.03/8.73  tff(c_25523, plain, (![A_1333]: (A_1333!='#skF_16')), inference(splitLeft, [status(thm)], [c_25522])).
% 21.03/8.73  tff(c_25548, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25523, c_13393])).
% 21.03/8.73  tff(c_25550, plain, (![B_1337]: (~r2_hidden(B_1337, '#skF_16'))), inference(splitRight, [status(thm)], [c_25522])).
% 21.03/8.73  tff(c_26094, plain, (![C_1350, B_1351]: (~r2_hidden(C_1350, k2_relat_1('#skF_15'('#skF_16', B_1351))))), inference(resolution, [status(thm)], [c_13857, c_25550])).
% 21.03/8.73  tff(c_26215, plain, $false, inference(resolution, [status(thm)], [c_24874, c_26094])).
% 21.03/8.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.03/8.73  
% 21.03/8.73  Inference rules
% 21.03/8.73  ----------------------
% 21.03/8.73  #Ref     : 1
% 21.03/8.73  #Sup     : 7160
% 21.03/8.73  #Fact    : 2
% 21.03/8.73  #Define  : 0
% 21.03/8.73  #Split   : 6
% 21.03/8.73  #Chain   : 0
% 21.03/8.73  #Close   : 0
% 21.03/8.73  
% 21.03/8.73  Ordering : KBO
% 21.03/8.73  
% 21.03/8.73  Simplification rules
% 21.03/8.73  ----------------------
% 21.03/8.73  #Subsume      : 1706
% 21.03/8.73  #Demod        : 918
% 21.03/8.73  #Tautology    : 588
% 21.03/8.73  #SimpNegUnit  : 20
% 21.03/8.73  #BackRed      : 11
% 21.03/8.73  
% 21.03/8.73  #Partial instantiations: 0
% 21.03/8.73  #Strategies tried      : 1
% 21.03/8.73  
% 21.03/8.73  Timing (in seconds)
% 21.03/8.73  ----------------------
% 21.03/8.74  Preprocessing        : 0.53
% 21.03/8.74  Parsing              : 0.26
% 21.03/8.74  CNF conversion       : 0.05
% 21.03/8.74  Main loop            : 7.38
% 21.03/8.74  Inferencing          : 1.63
% 21.03/8.74  Reduction            : 1.42
% 21.03/8.74  Demodulation         : 1.03
% 21.03/8.74  BG Simplification    : 0.22
% 21.03/8.74  Subsumption          : 3.60
% 21.03/8.74  Abstraction          : 0.25
% 21.03/8.74  MUC search           : 0.00
% 21.03/8.74  Cooper               : 0.00
% 21.03/8.74  Total                : 7.96
% 21.03/8.74  Index Insertion      : 0.00
% 21.03/8.74  Index Deletion       : 0.00
% 21.03/8.74  Index Matching       : 0.00
% 21.03/8.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
