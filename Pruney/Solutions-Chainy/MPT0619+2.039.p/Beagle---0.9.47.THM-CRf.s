%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:56 EST 2020

% Result     : Theorem 50.33s
% Output     : CNFRefutation 50.47s
% Verified   : 
% Statistics : Number of formulae       :  152 (2612 expanded)
%              Number of leaves         :   33 ( 918 expanded)
%              Depth                    :   30
%              Number of atoms          :  339 (6933 expanded)
%              Number of equality atoms :  176 (3489 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_tarski > k2_xboole_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_10 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_50,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_107,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( k1_relat_1(B) = k1_tarski(A)
         => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k1_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_relat_1)).

tff(f_88,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_65,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_237117,plain,(
    ! [A_187892,B_187893] :
      ( k2_xboole_0(k1_tarski(A_187892),B_187893) = B_187893
      | ~ r2_hidden(A_187892,B_187893) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_62,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_104,plain,(
    ! [A_68] :
      ( k2_relat_1(A_68) != k1_xboole_0
      | k1_xboole_0 = A_68
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_108,plain,
    ( k2_relat_1('#skF_10') != k1_xboole_0
    | k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_62,c_104])).

tff(c_109,plain,(
    k2_relat_1('#skF_10') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_98,plain,(
    ! [A_67] :
      ( k1_relat_1(A_67) != k1_xboole_0
      | k1_xboole_0 = A_67
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_102,plain,
    ( k1_relat_1('#skF_10') != k1_xboole_0
    | k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_62,c_98])).

tff(c_103,plain,(
    k1_relat_1('#skF_10') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_58,plain,(
    k1_tarski('#skF_9') = k1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_110,plain,(
    ! [A_69,B_70] :
      ( k2_xboole_0(k1_tarski(A_69),B_70) = B_70
      | ~ r2_hidden(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_20,plain,(
    ! [A_11,B_12] : k2_xboole_0(k1_tarski(A_11),B_12) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_136,plain,(
    ! [B_72,A_73] :
      ( k1_xboole_0 != B_72
      | ~ r2_hidden(A_73,B_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_20])).

tff(c_144,plain,(
    ! [C_5] : k1_tarski(C_5) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_136])).

tff(c_149,plain,(
    ! [A_77,B_78] :
      ( r2_hidden('#skF_3'(A_77,B_78),A_77)
      | k1_xboole_0 = A_77
      | k1_tarski(B_78) = A_77 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_160,plain,(
    ! [A_1,B_78] :
      ( '#skF_3'(k1_tarski(A_1),B_78) = A_1
      | k1_tarski(A_1) = k1_xboole_0
      | k1_tarski(B_78) = k1_tarski(A_1) ) ),
    inference(resolution,[status(thm)],[c_149,c_2])).

tff(c_170,plain,(
    ! [A_81,B_82] :
      ( '#skF_3'(k1_tarski(A_81),B_82) = A_81
      | k1_tarski(B_82) = k1_tarski(A_81) ) ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_160])).

tff(c_184,plain,(
    ! [B_82] :
      ( '#skF_3'(k1_relat_1('#skF_10'),B_82) = '#skF_9'
      | k1_tarski(B_82) = k1_tarski('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_170])).

tff(c_194,plain,(
    ! [B_83] :
      ( '#skF_3'(k1_relat_1('#skF_10'),B_83) = '#skF_9'
      | k1_tarski(B_83) = k1_relat_1('#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_184])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( '#skF_3'(A_6,B_7) != B_7
      | k1_xboole_0 = A_6
      | k1_tarski(B_7) = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_202,plain,(
    ! [B_83] :
      ( B_83 != '#skF_9'
      | k1_relat_1('#skF_10') = k1_xboole_0
      | k1_tarski(B_83) = k1_relat_1('#skF_10')
      | k1_tarski(B_83) = k1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_14])).

tff(c_209,plain,(
    ! [B_83] :
      ( B_83 != '#skF_9'
      | k1_tarski(B_83) = k1_relat_1('#skF_10')
      | k1_tarski(B_83) = k1_relat_1('#skF_10') ) ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_202])).

tff(c_247,plain,(
    ! [B_85] :
      ( B_85 != '#skF_9'
      | k1_tarski(B_85) = k1_relat_1('#skF_10') ) ),
    inference(factorization,[status(thm),theory(equality)],[c_209])).

tff(c_269,plain,(
    ! [B_85] :
      ( r2_hidden(B_85,k1_relat_1('#skF_10'))
      | B_85 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_4])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_4'(A_13,B_14),k2_relat_1(B_14))
      | ~ r2_hidden(A_13,k1_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_60,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_36,plain,(
    ! [A_17,C_53] :
      ( r2_hidden('#skF_8'(A_17,k2_relat_1(A_17),C_53),k1_relat_1(A_17))
      | ~ r2_hidden(C_53,k2_relat_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_32,plain,(
    ! [A_17,D_56] :
      ( r2_hidden(k1_funct_1(A_17,D_56),k2_relat_1(A_17))
      | ~ r2_hidden(D_56,k1_relat_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_135,plain,(
    ! [A_69] : ~ r2_hidden(A_69,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_20])).

tff(c_275,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_4])).

tff(c_5151,plain,(
    ! [A_7801,B_7802] :
      ( r2_hidden('#skF_6'(A_7801,B_7802),k1_relat_1(A_7801))
      | r2_hidden('#skF_7'(A_7801,B_7802),B_7802)
      | k2_relat_1(A_7801) = B_7802
      | ~ v1_funct_1(A_7801)
      | ~ v1_relat_1(A_7801) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_83,plain,(
    ! [C_64,A_65] :
      ( C_64 = A_65
      | ~ r2_hidden(C_64,k1_tarski(A_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_89,plain,(
    ! [C_64] :
      ( C_64 = '#skF_9'
      | ~ r2_hidden(C_64,k1_relat_1('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_83])).

tff(c_5169,plain,(
    ! [B_7802] :
      ( '#skF_6'('#skF_10',B_7802) = '#skF_9'
      | r2_hidden('#skF_7'('#skF_10',B_7802),B_7802)
      | k2_relat_1('#skF_10') = B_7802
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_5151,c_89])).

tff(c_5583,plain,(
    ! [B_8279] :
      ( '#skF_6'('#skF_10',B_8279) = '#skF_9'
      | r2_hidden('#skF_7'('#skF_10',B_8279),B_8279)
      | k2_relat_1('#skF_10') = B_8279 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_5169])).

tff(c_115,plain,(
    ! [B_70,A_69] :
      ( k1_xboole_0 != B_70
      | ~ r2_hidden(A_69,B_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_20])).

tff(c_6035,plain,
    ( '#skF_6'('#skF_10',k1_xboole_0) = '#skF_9'
    | k2_relat_1('#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5583,c_115])).

tff(c_6038,plain,(
    ! [D_56] :
      ( r2_hidden(k1_funct_1('#skF_10',D_56),k1_xboole_0)
      | ~ r2_hidden(D_56,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | '#skF_6'('#skF_10',k1_xboole_0) = '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6035,c_32])).

tff(c_6216,plain,(
    ! [D_56] :
      ( r2_hidden(k1_funct_1('#skF_10',D_56),k1_xboole_0)
      | ~ r2_hidden(D_56,k1_relat_1('#skF_10'))
      | '#skF_6'('#skF_10',k1_xboole_0) = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_6038])).

tff(c_6217,plain,(
    ! [D_56] :
      ( ~ r2_hidden(D_56,k1_relat_1('#skF_10'))
      | '#skF_6'('#skF_10',k1_xboole_0) = '#skF_9' ) ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_6216])).

tff(c_6228,plain,(
    ! [D_56] : ~ r2_hidden(D_56,k1_relat_1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_6217])).

tff(c_6231,plain,(
    ! [B_85] : B_85 != '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_6228,c_269])).

tff(c_167,plain,(
    ! [A_1,B_78] :
      ( '#skF_3'(k1_tarski(A_1),B_78) = A_1
      | k1_tarski(B_78) = k1_tarski(A_1) ) ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_160])).

tff(c_404,plain,(
    ! [B_100,B_101] :
      ( B_100 = '#skF_3'(k1_relat_1('#skF_10'),B_101)
      | k1_tarski(B_101) = k1_tarski(B_100)
      | B_100 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_167])).

tff(c_1019,plain,(
    ! [B_1158,B_1159] :
      ( r2_hidden(B_1158,k1_tarski(B_1159))
      | B_1158 = '#skF_3'(k1_relat_1('#skF_10'),B_1159)
      | B_1158 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_404,c_4])).

tff(c_1064,plain,(
    ! [B_1159,B_1158] :
      ( B_1159 = B_1158
      | B_1158 = '#skF_3'(k1_relat_1('#skF_10'),B_1159)
      | B_1158 != '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_1019,c_2])).

tff(c_1068,plain,(
    ! [B_1159] :
      ( B_1159 = '#skF_9'
      | '#skF_3'(k1_relat_1('#skF_10'),B_1159) = '#skF_9' ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1064])).

tff(c_6396,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6231,c_6231,c_1068])).

tff(c_6397,plain,(
    '#skF_6'('#skF_10',k1_xboole_0) = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_6217])).

tff(c_6564,plain,(
    ! [A_11902,B_11903] :
      ( k1_funct_1(A_11902,'#skF_6'(A_11902,B_11903)) = '#skF_5'(A_11902,B_11903)
      | r2_hidden('#skF_7'(A_11902,B_11903),B_11903)
      | k2_relat_1(A_11902) = B_11903
      | ~ v1_funct_1(A_11902)
      | ~ v1_relat_1(A_11902) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_54829,plain,(
    ! [A_34943,B_34944] :
      ( r2_hidden('#skF_5'(A_34943,B_34944),k2_relat_1(A_34943))
      | ~ r2_hidden('#skF_6'(A_34943,B_34944),k1_relat_1(A_34943))
      | ~ v1_funct_1(A_34943)
      | ~ v1_relat_1(A_34943)
      | r2_hidden('#skF_7'(A_34943,B_34944),B_34944)
      | k2_relat_1(A_34943) = B_34944
      | ~ v1_funct_1(A_34943)
      | ~ v1_relat_1(A_34943) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6564,c_32])).

tff(c_55003,plain,
    ( r2_hidden('#skF_5'('#skF_10',k1_xboole_0),k2_relat_1('#skF_10'))
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10')
    | r2_hidden('#skF_7'('#skF_10',k1_xboole_0),k1_xboole_0)
    | k2_relat_1('#skF_10') = k1_xboole_0
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_6397,c_54829])).

tff(c_55076,plain,
    ( r2_hidden('#skF_5'('#skF_10',k1_xboole_0),k2_relat_1('#skF_10'))
    | r2_hidden('#skF_7'('#skF_10',k1_xboole_0),k1_xboole_0)
    | k2_relat_1('#skF_10') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_62,c_60,c_275,c_55003])).

tff(c_55077,plain,(
    r2_hidden('#skF_5'('#skF_10',k1_xboole_0),k2_relat_1('#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_135,c_55076])).

tff(c_4265,plain,(
    ! [A_6453,C_6454] :
      ( r2_hidden('#skF_8'(A_6453,k2_relat_1(A_6453),C_6454),k1_relat_1(A_6453))
      | ~ r2_hidden(C_6454,k2_relat_1(A_6453))
      | ~ v1_funct_1(A_6453)
      | ~ v1_relat_1(A_6453) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4283,plain,(
    ! [C_6454] :
      ( '#skF_8'('#skF_10',k2_relat_1('#skF_10'),C_6454) = '#skF_9'
      | ~ r2_hidden(C_6454,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_4265,c_89])).

tff(c_4347,plain,(
    ! [C_6454] :
      ( '#skF_8'('#skF_10',k2_relat_1('#skF_10'),C_6454) = '#skF_9'
      | ~ r2_hidden(C_6454,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_4283])).

tff(c_55355,plain,(
    '#skF_8'('#skF_10',k2_relat_1('#skF_10'),'#skF_5'('#skF_10',k1_xboole_0)) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_55077,c_4347])).

tff(c_34,plain,(
    ! [A_17,C_53] :
      ( k1_funct_1(A_17,'#skF_8'(A_17,k2_relat_1(A_17),C_53)) = C_53
      | ~ r2_hidden(C_53,k2_relat_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_55367,plain,
    ( k1_funct_1('#skF_10','#skF_9') = '#skF_5'('#skF_10',k1_xboole_0)
    | ~ r2_hidden('#skF_5'('#skF_10',k1_xboole_0),k2_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_55355,c_34])).

tff(c_55758,plain,(
    k1_funct_1('#skF_10','#skF_9') = '#skF_5'('#skF_10',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_55077,c_55367])).

tff(c_4360,plain,(
    ! [C_6533] :
      ( '#skF_8'('#skF_10',k2_relat_1('#skF_10'),C_6533) = '#skF_9'
      | ~ r2_hidden(C_6533,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_4283])).

tff(c_4368,plain,(
    ! [D_56] :
      ( '#skF_8'('#skF_10',k2_relat_1('#skF_10'),k1_funct_1('#skF_10',D_56)) = '#skF_9'
      | ~ r2_hidden(D_56,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_32,c_4360])).

tff(c_4484,plain,(
    ! [D_6930] :
      ( '#skF_8'('#skF_10',k2_relat_1('#skF_10'),k1_funct_1('#skF_10',D_6930)) = '#skF_9'
      | ~ r2_hidden(D_6930,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_4368])).

tff(c_4493,plain,(
    ! [D_6930] :
      ( k1_funct_1('#skF_10',D_6930) = k1_funct_1('#skF_10','#skF_9')
      | ~ r2_hidden(k1_funct_1('#skF_10',D_6930),k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(D_6930,k1_relat_1('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4484,c_34])).

tff(c_4517,plain,(
    ! [D_6930] :
      ( k1_funct_1('#skF_10',D_6930) = k1_funct_1('#skF_10','#skF_9')
      | ~ r2_hidden(k1_funct_1('#skF_10',D_6930),k2_relat_1('#skF_10'))
      | ~ r2_hidden(D_6930,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_4493])).

tff(c_168656,plain,(
    ! [D_141591] :
      ( k1_funct_1('#skF_10',D_141591) = '#skF_5'('#skF_10',k1_xboole_0)
      | ~ r2_hidden(k1_funct_1('#skF_10',D_141591),k2_relat_1('#skF_10'))
      | ~ r2_hidden(D_141591,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55758,c_4517])).

tff(c_168924,plain,(
    ! [D_56] :
      ( k1_funct_1('#skF_10',D_56) = '#skF_5'('#skF_10',k1_xboole_0)
      | ~ r2_hidden(D_56,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_32,c_168656])).

tff(c_168946,plain,(
    ! [D_142034] :
      ( k1_funct_1('#skF_10',D_142034) = '#skF_5'('#skF_10',k1_xboole_0)
      | ~ r2_hidden(D_142034,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_168924])).

tff(c_169218,plain,(
    ! [C_53] :
      ( k1_funct_1('#skF_10','#skF_8'('#skF_10',k2_relat_1('#skF_10'),C_53)) = '#skF_5'('#skF_10',k1_xboole_0)
      | ~ r2_hidden(C_53,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_36,c_168946])).

tff(c_183230,plain,(
    ! [C_153225] :
      ( k1_funct_1('#skF_10','#skF_8'('#skF_10',k2_relat_1('#skF_10'),C_153225)) = '#skF_5'('#skF_10',k1_xboole_0)
      | ~ r2_hidden(C_153225,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_169218])).

tff(c_183258,plain,(
    ! [C_153225] :
      ( C_153225 = '#skF_5'('#skF_10',k1_xboole_0)
      | ~ r2_hidden(C_153225,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(C_153225,k2_relat_1('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183230,c_34])).

tff(c_184143,plain,(
    ! [C_153694] :
      ( C_153694 = '#skF_5'('#skF_10',k1_xboole_0)
      | ~ r2_hidden(C_153694,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_183258])).

tff(c_184370,plain,(
    ! [A_13] :
      ( '#skF_5'('#skF_10',k1_xboole_0) = '#skF_4'(A_13,'#skF_10')
      | ~ r2_hidden(A_13,k1_relat_1('#skF_10'))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_22,c_184143])).

tff(c_184417,plain,(
    ! [A_154163] :
      ( '#skF_5'('#skF_10',k1_xboole_0) = '#skF_4'(A_154163,'#skF_10')
      | ~ r2_hidden(A_154163,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_184370])).

tff(c_184798,plain,(
    ! [B_154632] :
      ( '#skF_5'('#skF_10',k1_xboole_0) = '#skF_4'(B_154632,'#skF_10')
      | B_154632 != '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_269,c_184417])).

tff(c_5658,plain,(
    ! [B_8358] :
      ( k1_xboole_0 != B_8358
      | '#skF_6'('#skF_10',B_8358) = '#skF_9'
      | k2_relat_1('#skF_10') = B_8358 ) ),
    inference(resolution,[status(thm)],[c_5583,c_115])).

tff(c_6129,plain,(
    ! [B_8358] :
      ( k1_xboole_0 != B_8358
      | k1_xboole_0 != B_8358
      | '#skF_6'('#skF_10',B_8358) = '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5658,c_109])).

tff(c_72373,plain,(
    ! [B_51499,A_51500] :
      ( k1_xboole_0 != B_51499
      | k1_funct_1(A_51500,'#skF_6'(A_51500,B_51499)) = '#skF_5'(A_51500,B_51499)
      | k2_relat_1(A_51500) = B_51499
      | ~ v1_funct_1(A_51500)
      | ~ v1_relat_1(A_51500) ) ),
    inference(resolution,[status(thm)],[c_6564,c_115])).

tff(c_72835,plain,(
    ! [B_8358] :
      ( k1_xboole_0 != B_8358
      | k1_funct_1('#skF_10','#skF_9') = '#skF_5'('#skF_10',B_8358)
      | k2_relat_1('#skF_10') = B_8358
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | k1_xboole_0 != B_8358
      | k1_xboole_0 != B_8358 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6129,c_72373])).

tff(c_73022,plain,(
    ! [B_51918] :
      ( '#skF_5'('#skF_10',k1_xboole_0) = '#skF_5'('#skF_10',B_51918)
      | k2_relat_1('#skF_10') = B_51918
      | k1_xboole_0 != B_51918 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_55758,c_72835])).

tff(c_75186,plain,(
    ! [B_57769] :
      ( k1_xboole_0 != B_57769
      | '#skF_5'('#skF_10',k1_xboole_0) = '#skF_5'('#skF_10',B_57769)
      | k1_xboole_0 != B_57769 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73022,c_109])).

tff(c_50,plain,(
    ! [A_57,C_59] :
      ( r2_hidden(k4_tarski(A_57,k1_funct_1(C_59,A_57)),C_59)
      | ~ r2_hidden(A_57,k1_relat_1(C_59))
      | ~ v1_funct_1(C_59)
      | ~ v1_relat_1(C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_6572,plain,(
    ! [A_11902,B_11903] :
      ( r2_hidden(k4_tarski('#skF_6'(A_11902,B_11903),'#skF_5'(A_11902,B_11903)),A_11902)
      | ~ r2_hidden('#skF_6'(A_11902,B_11903),k1_relat_1(A_11902))
      | ~ v1_funct_1(A_11902)
      | ~ v1_relat_1(A_11902)
      | r2_hidden('#skF_7'(A_11902,B_11903),B_11903)
      | k2_relat_1(A_11902) = B_11903
      | ~ v1_funct_1(A_11902)
      | ~ v1_relat_1(A_11902) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6564,c_50])).

tff(c_75209,plain,(
    ! [B_57769] :
      ( r2_hidden(k4_tarski('#skF_6'('#skF_10',k1_xboole_0),'#skF_5'('#skF_10',B_57769)),'#skF_10')
      | ~ r2_hidden('#skF_6'('#skF_10',k1_xboole_0),k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | r2_hidden('#skF_7'('#skF_10',k1_xboole_0),k1_xboole_0)
      | k2_relat_1('#skF_10') = k1_xboole_0
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | k1_xboole_0 != B_57769
      | k1_xboole_0 != B_57769 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75186,c_6572])).

tff(c_75570,plain,(
    ! [B_57769] :
      ( r2_hidden(k4_tarski('#skF_9','#skF_5'('#skF_10',B_57769)),'#skF_10')
      | r2_hidden('#skF_7'('#skF_10',k1_xboole_0),k1_xboole_0)
      | k2_relat_1('#skF_10') = k1_xboole_0
      | k1_xboole_0 != B_57769 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_62,c_60,c_275,c_6397,c_6397,c_75209])).

tff(c_75688,plain,(
    ! [B_58474] :
      ( r2_hidden(k4_tarski('#skF_9','#skF_5'('#skF_10',B_58474)),'#skF_10')
      | k1_xboole_0 != B_58474 ) ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_135,c_75570])).

tff(c_52,plain,(
    ! [C_59,A_57,B_58] :
      ( k1_funct_1(C_59,A_57) = B_58
      | ~ r2_hidden(k4_tarski(A_57,B_58),C_59)
      | ~ v1_funct_1(C_59)
      | ~ v1_relat_1(C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_75698,plain,(
    ! [B_58474] :
      ( k1_funct_1('#skF_10','#skF_9') = '#skF_5'('#skF_10',B_58474)
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | k1_xboole_0 != B_58474 ) ),
    inference(resolution,[status(thm)],[c_75688,c_52])).

tff(c_76155,plain,(
    ! [B_58474] :
      ( '#skF_5'('#skF_10',k1_xboole_0) = '#skF_5'('#skF_10',B_58474)
      | k1_xboole_0 != B_58474 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_55758,c_75698])).

tff(c_76163,plain,(
    ! [B_58709] :
      ( '#skF_5'('#skF_10',k1_xboole_0) = '#skF_5'('#skF_10',B_58709)
      | k1_xboole_0 != B_58709 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_55758,c_75698])).

tff(c_76222,plain,(
    ! [B_58709,B_58474] :
      ( '#skF_5'('#skF_10',B_58709) = '#skF_5'('#skF_10',B_58474)
      | k1_xboole_0 != B_58709
      | k1_xboole_0 != B_58474 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76155,c_76163])).

tff(c_212471,plain,(
    '#skF_5'('#skF_10',k1_xboole_0) = '#skF_4'('#skF_9','#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_184798,c_76222])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_3'(A_6,B_7),A_6)
      | k1_xboole_0 = A_6
      | k1_tarski(B_7) = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_184374,plain,(
    ! [B_7] :
      ( '#skF_3'(k2_relat_1('#skF_10'),B_7) = '#skF_5'('#skF_10',k1_xboole_0)
      | k2_relat_1('#skF_10') = k1_xboole_0
      | k2_relat_1('#skF_10') = k1_tarski(B_7) ) ),
    inference(resolution,[status(thm)],[c_16,c_184143])).

tff(c_184416,plain,(
    ! [B_7] :
      ( '#skF_3'(k2_relat_1('#skF_10'),B_7) = '#skF_5'('#skF_10',k1_xboole_0)
      | k2_relat_1('#skF_10') = k1_tarski(B_7) ) ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_184374])).

tff(c_218464,plain,(
    ! [B_183429] :
      ( '#skF_3'(k2_relat_1('#skF_10'),B_183429) = '#skF_4'('#skF_9','#skF_10')
      | k2_relat_1('#skF_10') = k1_tarski(B_183429) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212471,c_184416])).

tff(c_218490,plain,(
    ! [B_183429] :
      ( B_183429 != '#skF_4'('#skF_9','#skF_10')
      | k2_relat_1('#skF_10') = k1_xboole_0
      | k2_relat_1('#skF_10') = k1_tarski(B_183429)
      | k2_relat_1('#skF_10') = k1_tarski(B_183429) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_218464,c_14])).

tff(c_237035,plain,(
    k1_tarski('#skF_4'('#skF_9','#skF_10')) = k2_relat_1('#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_218490])).

tff(c_184759,plain,(
    '#skF_5'('#skF_10',k1_xboole_0) = '#skF_4'('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_269,c_184417])).

tff(c_56,plain,(
    k1_tarski(k1_funct_1('#skF_10','#skF_9')) != k2_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_55776,plain,(
    k1_tarski('#skF_5'('#skF_10',k1_xboole_0)) != k2_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55758,c_56])).

tff(c_184797,plain,(
    k1_tarski('#skF_4'('#skF_9','#skF_10')) != k2_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_184759,c_55776])).

tff(c_237040,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_237035,c_184797])).

tff(c_237041,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_237044,plain,(
    k1_relat_1('#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_237041,c_103])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_237049,plain,(
    k1_relat_1('#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_237041,c_237041,c_26])).

tff(c_237060,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_237044,c_237049])).

tff(c_237061,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_237065,plain,(
    ! [A_11,B_12] : k2_xboole_0(k1_tarski(A_11),B_12) != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_237061,c_20])).

tff(c_237131,plain,(
    ! [A_187892] : ~ r2_hidden(A_187892,'#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_237117,c_237065])).

tff(c_237062,plain,(
    k1_relat_1('#skF_10') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_237072,plain,(
    k1_relat_1('#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_237061,c_237062])).

tff(c_75,plain,(
    ! [C_60] : r2_hidden(C_60,k1_tarski(C_60)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_78,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_75])).

tff(c_237074,plain,(
    r2_hidden('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_237072,c_78])).

tff(c_237133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_237131,c_237074])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:22:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 50.33/36.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 50.37/36.90  
% 50.37/36.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 50.37/36.90  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_tarski > k2_xboole_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_10 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_4
% 50.37/36.90  
% 50.37/36.90  %Foreground sorts:
% 50.37/36.90  
% 50.37/36.90  
% 50.37/36.90  %Background operators:
% 50.37/36.90  
% 50.37/36.90  
% 50.37/36.90  %Foreground operators:
% 50.37/36.90  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 50.37/36.90  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 50.37/36.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 50.37/36.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 50.37/36.90  tff(k1_tarski, type, k1_tarski: $i > $i).
% 50.37/36.90  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 50.37/36.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 50.37/36.90  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 50.37/36.90  tff('#skF_10', type, '#skF_10': $i).
% 50.37/36.90  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 50.37/36.90  tff('#skF_9', type, '#skF_9': $i).
% 50.37/36.90  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 50.37/36.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 50.37/36.90  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 50.37/36.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 50.37/36.90  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 50.37/36.90  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 50.37/36.90  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 50.37/36.90  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 50.37/36.90  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 50.37/36.90  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 50.37/36.90  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 50.37/36.90  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 50.37/36.90  
% 50.47/36.93  tff(f_50, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 50.47/36.93  tff(f_107, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 50.47/36.93  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 50.47/36.93  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 50.47/36.93  tff(f_53, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 50.47/36.93  tff(f_46, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 50.47/36.93  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k1_relat_1(B)) & (![C]: ~r2_hidden(C, k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_relat_1)).
% 50.47/36.93  tff(f_88, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 50.47/36.93  tff(f_98, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 50.47/36.93  tff(f_65, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 50.47/36.93  tff(c_237117, plain, (![A_187892, B_187893]: (k2_xboole_0(k1_tarski(A_187892), B_187893)=B_187893 | ~r2_hidden(A_187892, B_187893))), inference(cnfTransformation, [status(thm)], [f_50])).
% 50.47/36.93  tff(c_62, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_107])).
% 50.47/36.93  tff(c_104, plain, (![A_68]: (k2_relat_1(A_68)!=k1_xboole_0 | k1_xboole_0=A_68 | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_73])).
% 50.47/36.93  tff(c_108, plain, (k2_relat_1('#skF_10')!=k1_xboole_0 | k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_62, c_104])).
% 50.47/36.93  tff(c_109, plain, (k2_relat_1('#skF_10')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_108])).
% 50.47/36.93  tff(c_98, plain, (![A_67]: (k1_relat_1(A_67)!=k1_xboole_0 | k1_xboole_0=A_67 | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_73])).
% 50.47/36.93  tff(c_102, plain, (k1_relat_1('#skF_10')!=k1_xboole_0 | k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_62, c_98])).
% 50.47/36.93  tff(c_103, plain, (k1_relat_1('#skF_10')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_102])).
% 50.47/36.93  tff(c_58, plain, (k1_tarski('#skF_9')=k1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_107])).
% 50.47/36.93  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 50.47/36.93  tff(c_110, plain, (![A_69, B_70]: (k2_xboole_0(k1_tarski(A_69), B_70)=B_70 | ~r2_hidden(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_50])).
% 50.47/36.93  tff(c_20, plain, (![A_11, B_12]: (k2_xboole_0(k1_tarski(A_11), B_12)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 50.47/36.93  tff(c_136, plain, (![B_72, A_73]: (k1_xboole_0!=B_72 | ~r2_hidden(A_73, B_72))), inference(superposition, [status(thm), theory('equality')], [c_110, c_20])).
% 50.47/36.93  tff(c_144, plain, (![C_5]: (k1_tarski(C_5)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_136])).
% 50.47/36.93  tff(c_149, plain, (![A_77, B_78]: (r2_hidden('#skF_3'(A_77, B_78), A_77) | k1_xboole_0=A_77 | k1_tarski(B_78)=A_77)), inference(cnfTransformation, [status(thm)], [f_46])).
% 50.47/36.93  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 50.47/36.93  tff(c_160, plain, (![A_1, B_78]: ('#skF_3'(k1_tarski(A_1), B_78)=A_1 | k1_tarski(A_1)=k1_xboole_0 | k1_tarski(B_78)=k1_tarski(A_1))), inference(resolution, [status(thm)], [c_149, c_2])).
% 50.47/36.93  tff(c_170, plain, (![A_81, B_82]: ('#skF_3'(k1_tarski(A_81), B_82)=A_81 | k1_tarski(B_82)=k1_tarski(A_81))), inference(negUnitSimplification, [status(thm)], [c_144, c_160])).
% 50.47/36.93  tff(c_184, plain, (![B_82]: ('#skF_3'(k1_relat_1('#skF_10'), B_82)='#skF_9' | k1_tarski(B_82)=k1_tarski('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_170])).
% 50.47/36.93  tff(c_194, plain, (![B_83]: ('#skF_3'(k1_relat_1('#skF_10'), B_83)='#skF_9' | k1_tarski(B_83)=k1_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_184])).
% 50.47/36.93  tff(c_14, plain, (![A_6, B_7]: ('#skF_3'(A_6, B_7)!=B_7 | k1_xboole_0=A_6 | k1_tarski(B_7)=A_6)), inference(cnfTransformation, [status(thm)], [f_46])).
% 50.47/36.93  tff(c_202, plain, (![B_83]: (B_83!='#skF_9' | k1_relat_1('#skF_10')=k1_xboole_0 | k1_tarski(B_83)=k1_relat_1('#skF_10') | k1_tarski(B_83)=k1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_194, c_14])).
% 50.47/36.93  tff(c_209, plain, (![B_83]: (B_83!='#skF_9' | k1_tarski(B_83)=k1_relat_1('#skF_10') | k1_tarski(B_83)=k1_relat_1('#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_103, c_202])).
% 50.47/36.93  tff(c_247, plain, (![B_85]: (B_85!='#skF_9' | k1_tarski(B_85)=k1_relat_1('#skF_10'))), inference(factorization, [status(thm), theory('equality')], [c_209])).
% 50.47/36.93  tff(c_269, plain, (![B_85]: (r2_hidden(B_85, k1_relat_1('#skF_10')) | B_85!='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_247, c_4])).
% 50.47/36.93  tff(c_22, plain, (![A_13, B_14]: (r2_hidden('#skF_4'(A_13, B_14), k2_relat_1(B_14)) | ~r2_hidden(A_13, k1_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 50.47/36.93  tff(c_60, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_107])).
% 50.47/36.93  tff(c_36, plain, (![A_17, C_53]: (r2_hidden('#skF_8'(A_17, k2_relat_1(A_17), C_53), k1_relat_1(A_17)) | ~r2_hidden(C_53, k2_relat_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_88])).
% 50.47/36.93  tff(c_32, plain, (![A_17, D_56]: (r2_hidden(k1_funct_1(A_17, D_56), k2_relat_1(A_17)) | ~r2_hidden(D_56, k1_relat_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_88])).
% 50.47/36.93  tff(c_135, plain, (![A_69]: (~r2_hidden(A_69, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_110, c_20])).
% 50.47/36.93  tff(c_275, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_247, c_4])).
% 50.47/36.93  tff(c_5151, plain, (![A_7801, B_7802]: (r2_hidden('#skF_6'(A_7801, B_7802), k1_relat_1(A_7801)) | r2_hidden('#skF_7'(A_7801, B_7802), B_7802) | k2_relat_1(A_7801)=B_7802 | ~v1_funct_1(A_7801) | ~v1_relat_1(A_7801))), inference(cnfTransformation, [status(thm)], [f_88])).
% 50.47/36.93  tff(c_83, plain, (![C_64, A_65]: (C_64=A_65 | ~r2_hidden(C_64, k1_tarski(A_65)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 50.47/36.93  tff(c_89, plain, (![C_64]: (C_64='#skF_9' | ~r2_hidden(C_64, k1_relat_1('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_58, c_83])).
% 50.47/36.93  tff(c_5169, plain, (![B_7802]: ('#skF_6'('#skF_10', B_7802)='#skF_9' | r2_hidden('#skF_7'('#skF_10', B_7802), B_7802) | k2_relat_1('#skF_10')=B_7802 | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_5151, c_89])).
% 50.47/36.93  tff(c_5583, plain, (![B_8279]: ('#skF_6'('#skF_10', B_8279)='#skF_9' | r2_hidden('#skF_7'('#skF_10', B_8279), B_8279) | k2_relat_1('#skF_10')=B_8279)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_5169])).
% 50.47/36.93  tff(c_115, plain, (![B_70, A_69]: (k1_xboole_0!=B_70 | ~r2_hidden(A_69, B_70))), inference(superposition, [status(thm), theory('equality')], [c_110, c_20])).
% 50.47/36.93  tff(c_6035, plain, ('#skF_6'('#skF_10', k1_xboole_0)='#skF_9' | k2_relat_1('#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_5583, c_115])).
% 50.47/36.93  tff(c_6038, plain, (![D_56]: (r2_hidden(k1_funct_1('#skF_10', D_56), k1_xboole_0) | ~r2_hidden(D_56, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | '#skF_6'('#skF_10', k1_xboole_0)='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_6035, c_32])).
% 50.47/36.93  tff(c_6216, plain, (![D_56]: (r2_hidden(k1_funct_1('#skF_10', D_56), k1_xboole_0) | ~r2_hidden(D_56, k1_relat_1('#skF_10')) | '#skF_6'('#skF_10', k1_xboole_0)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_6038])).
% 50.47/36.93  tff(c_6217, plain, (![D_56]: (~r2_hidden(D_56, k1_relat_1('#skF_10')) | '#skF_6'('#skF_10', k1_xboole_0)='#skF_9')), inference(negUnitSimplification, [status(thm)], [c_135, c_6216])).
% 50.47/36.93  tff(c_6228, plain, (![D_56]: (~r2_hidden(D_56, k1_relat_1('#skF_10')))), inference(splitLeft, [status(thm)], [c_6217])).
% 50.47/36.93  tff(c_6231, plain, (![B_85]: (B_85!='#skF_9')), inference(negUnitSimplification, [status(thm)], [c_6228, c_269])).
% 50.47/36.93  tff(c_167, plain, (![A_1, B_78]: ('#skF_3'(k1_tarski(A_1), B_78)=A_1 | k1_tarski(B_78)=k1_tarski(A_1))), inference(negUnitSimplification, [status(thm)], [c_144, c_160])).
% 50.47/36.93  tff(c_404, plain, (![B_100, B_101]: (B_100='#skF_3'(k1_relat_1('#skF_10'), B_101) | k1_tarski(B_101)=k1_tarski(B_100) | B_100!='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_247, c_167])).
% 50.47/36.93  tff(c_1019, plain, (![B_1158, B_1159]: (r2_hidden(B_1158, k1_tarski(B_1159)) | B_1158='#skF_3'(k1_relat_1('#skF_10'), B_1159) | B_1158!='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_404, c_4])).
% 50.47/36.93  tff(c_1064, plain, (![B_1159, B_1158]: (B_1159=B_1158 | B_1158='#skF_3'(k1_relat_1('#skF_10'), B_1159) | B_1158!='#skF_9')), inference(resolution, [status(thm)], [c_1019, c_2])).
% 50.47/36.93  tff(c_1068, plain, (![B_1159]: (B_1159='#skF_9' | '#skF_3'(k1_relat_1('#skF_10'), B_1159)='#skF_9')), inference(reflexivity, [status(thm), theory('equality')], [c_1064])).
% 50.47/36.93  tff(c_6396, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6231, c_6231, c_1068])).
% 50.47/36.93  tff(c_6397, plain, ('#skF_6'('#skF_10', k1_xboole_0)='#skF_9'), inference(splitRight, [status(thm)], [c_6217])).
% 50.47/36.93  tff(c_6564, plain, (![A_11902, B_11903]: (k1_funct_1(A_11902, '#skF_6'(A_11902, B_11903))='#skF_5'(A_11902, B_11903) | r2_hidden('#skF_7'(A_11902, B_11903), B_11903) | k2_relat_1(A_11902)=B_11903 | ~v1_funct_1(A_11902) | ~v1_relat_1(A_11902))), inference(cnfTransformation, [status(thm)], [f_88])).
% 50.47/36.93  tff(c_54829, plain, (![A_34943, B_34944]: (r2_hidden('#skF_5'(A_34943, B_34944), k2_relat_1(A_34943)) | ~r2_hidden('#skF_6'(A_34943, B_34944), k1_relat_1(A_34943)) | ~v1_funct_1(A_34943) | ~v1_relat_1(A_34943) | r2_hidden('#skF_7'(A_34943, B_34944), B_34944) | k2_relat_1(A_34943)=B_34944 | ~v1_funct_1(A_34943) | ~v1_relat_1(A_34943))), inference(superposition, [status(thm), theory('equality')], [c_6564, c_32])).
% 50.47/36.93  tff(c_55003, plain, (r2_hidden('#skF_5'('#skF_10', k1_xboole_0), k2_relat_1('#skF_10')) | ~r2_hidden('#skF_9', k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | r2_hidden('#skF_7'('#skF_10', k1_xboole_0), k1_xboole_0) | k2_relat_1('#skF_10')=k1_xboole_0 | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_6397, c_54829])).
% 50.47/36.93  tff(c_55076, plain, (r2_hidden('#skF_5'('#skF_10', k1_xboole_0), k2_relat_1('#skF_10')) | r2_hidden('#skF_7'('#skF_10', k1_xboole_0), k1_xboole_0) | k2_relat_1('#skF_10')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_62, c_60, c_275, c_55003])).
% 50.47/36.93  tff(c_55077, plain, (r2_hidden('#skF_5'('#skF_10', k1_xboole_0), k2_relat_1('#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_109, c_135, c_55076])).
% 50.47/36.93  tff(c_4265, plain, (![A_6453, C_6454]: (r2_hidden('#skF_8'(A_6453, k2_relat_1(A_6453), C_6454), k1_relat_1(A_6453)) | ~r2_hidden(C_6454, k2_relat_1(A_6453)) | ~v1_funct_1(A_6453) | ~v1_relat_1(A_6453))), inference(cnfTransformation, [status(thm)], [f_88])).
% 50.47/36.93  tff(c_4283, plain, (![C_6454]: ('#skF_8'('#skF_10', k2_relat_1('#skF_10'), C_6454)='#skF_9' | ~r2_hidden(C_6454, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_4265, c_89])).
% 50.47/36.93  tff(c_4347, plain, (![C_6454]: ('#skF_8'('#skF_10', k2_relat_1('#skF_10'), C_6454)='#skF_9' | ~r2_hidden(C_6454, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_4283])).
% 50.47/36.93  tff(c_55355, plain, ('#skF_8'('#skF_10', k2_relat_1('#skF_10'), '#skF_5'('#skF_10', k1_xboole_0))='#skF_9'), inference(resolution, [status(thm)], [c_55077, c_4347])).
% 50.47/36.93  tff(c_34, plain, (![A_17, C_53]: (k1_funct_1(A_17, '#skF_8'(A_17, k2_relat_1(A_17), C_53))=C_53 | ~r2_hidden(C_53, k2_relat_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_88])).
% 50.47/36.93  tff(c_55367, plain, (k1_funct_1('#skF_10', '#skF_9')='#skF_5'('#skF_10', k1_xboole_0) | ~r2_hidden('#skF_5'('#skF_10', k1_xboole_0), k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_55355, c_34])).
% 50.47/36.93  tff(c_55758, plain, (k1_funct_1('#skF_10', '#skF_9')='#skF_5'('#skF_10', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_55077, c_55367])).
% 50.47/36.93  tff(c_4360, plain, (![C_6533]: ('#skF_8'('#skF_10', k2_relat_1('#skF_10'), C_6533)='#skF_9' | ~r2_hidden(C_6533, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_4283])).
% 50.47/36.93  tff(c_4368, plain, (![D_56]: ('#skF_8'('#skF_10', k2_relat_1('#skF_10'), k1_funct_1('#skF_10', D_56))='#skF_9' | ~r2_hidden(D_56, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_32, c_4360])).
% 50.47/36.93  tff(c_4484, plain, (![D_6930]: ('#skF_8'('#skF_10', k2_relat_1('#skF_10'), k1_funct_1('#skF_10', D_6930))='#skF_9' | ~r2_hidden(D_6930, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_4368])).
% 50.47/36.93  tff(c_4493, plain, (![D_6930]: (k1_funct_1('#skF_10', D_6930)=k1_funct_1('#skF_10', '#skF_9') | ~r2_hidden(k1_funct_1('#skF_10', D_6930), k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r2_hidden(D_6930, k1_relat_1('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_4484, c_34])).
% 50.47/36.93  tff(c_4517, plain, (![D_6930]: (k1_funct_1('#skF_10', D_6930)=k1_funct_1('#skF_10', '#skF_9') | ~r2_hidden(k1_funct_1('#skF_10', D_6930), k2_relat_1('#skF_10')) | ~r2_hidden(D_6930, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_4493])).
% 50.47/36.93  tff(c_168656, plain, (![D_141591]: (k1_funct_1('#skF_10', D_141591)='#skF_5'('#skF_10', k1_xboole_0) | ~r2_hidden(k1_funct_1('#skF_10', D_141591), k2_relat_1('#skF_10')) | ~r2_hidden(D_141591, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_55758, c_4517])).
% 50.47/36.93  tff(c_168924, plain, (![D_56]: (k1_funct_1('#skF_10', D_56)='#skF_5'('#skF_10', k1_xboole_0) | ~r2_hidden(D_56, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_32, c_168656])).
% 50.47/36.93  tff(c_168946, plain, (![D_142034]: (k1_funct_1('#skF_10', D_142034)='#skF_5'('#skF_10', k1_xboole_0) | ~r2_hidden(D_142034, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_168924])).
% 50.47/36.93  tff(c_169218, plain, (![C_53]: (k1_funct_1('#skF_10', '#skF_8'('#skF_10', k2_relat_1('#skF_10'), C_53))='#skF_5'('#skF_10', k1_xboole_0) | ~r2_hidden(C_53, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_36, c_168946])).
% 50.47/36.93  tff(c_183230, plain, (![C_153225]: (k1_funct_1('#skF_10', '#skF_8'('#skF_10', k2_relat_1('#skF_10'), C_153225))='#skF_5'('#skF_10', k1_xboole_0) | ~r2_hidden(C_153225, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_169218])).
% 50.47/36.93  tff(c_183258, plain, (![C_153225]: (C_153225='#skF_5'('#skF_10', k1_xboole_0) | ~r2_hidden(C_153225, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r2_hidden(C_153225, k2_relat_1('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_183230, c_34])).
% 50.47/36.93  tff(c_184143, plain, (![C_153694]: (C_153694='#skF_5'('#skF_10', k1_xboole_0) | ~r2_hidden(C_153694, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_183258])).
% 50.47/36.93  tff(c_184370, plain, (![A_13]: ('#skF_5'('#skF_10', k1_xboole_0)='#skF_4'(A_13, '#skF_10') | ~r2_hidden(A_13, k1_relat_1('#skF_10')) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_22, c_184143])).
% 50.47/36.93  tff(c_184417, plain, (![A_154163]: ('#skF_5'('#skF_10', k1_xboole_0)='#skF_4'(A_154163, '#skF_10') | ~r2_hidden(A_154163, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_184370])).
% 50.47/36.93  tff(c_184798, plain, (![B_154632]: ('#skF_5'('#skF_10', k1_xboole_0)='#skF_4'(B_154632, '#skF_10') | B_154632!='#skF_9')), inference(resolution, [status(thm)], [c_269, c_184417])).
% 50.47/36.93  tff(c_5658, plain, (![B_8358]: (k1_xboole_0!=B_8358 | '#skF_6'('#skF_10', B_8358)='#skF_9' | k2_relat_1('#skF_10')=B_8358)), inference(resolution, [status(thm)], [c_5583, c_115])).
% 50.47/36.93  tff(c_6129, plain, (![B_8358]: (k1_xboole_0!=B_8358 | k1_xboole_0!=B_8358 | '#skF_6'('#skF_10', B_8358)='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_5658, c_109])).
% 50.47/36.93  tff(c_72373, plain, (![B_51499, A_51500]: (k1_xboole_0!=B_51499 | k1_funct_1(A_51500, '#skF_6'(A_51500, B_51499))='#skF_5'(A_51500, B_51499) | k2_relat_1(A_51500)=B_51499 | ~v1_funct_1(A_51500) | ~v1_relat_1(A_51500))), inference(resolution, [status(thm)], [c_6564, c_115])).
% 50.47/36.93  tff(c_72835, plain, (![B_8358]: (k1_xboole_0!=B_8358 | k1_funct_1('#skF_10', '#skF_9')='#skF_5'('#skF_10', B_8358) | k2_relat_1('#skF_10')=B_8358 | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | k1_xboole_0!=B_8358 | k1_xboole_0!=B_8358)), inference(superposition, [status(thm), theory('equality')], [c_6129, c_72373])).
% 50.47/36.93  tff(c_73022, plain, (![B_51918]: ('#skF_5'('#skF_10', k1_xboole_0)='#skF_5'('#skF_10', B_51918) | k2_relat_1('#skF_10')=B_51918 | k1_xboole_0!=B_51918)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_55758, c_72835])).
% 50.47/36.93  tff(c_75186, plain, (![B_57769]: (k1_xboole_0!=B_57769 | '#skF_5'('#skF_10', k1_xboole_0)='#skF_5'('#skF_10', B_57769) | k1_xboole_0!=B_57769)), inference(superposition, [status(thm), theory('equality')], [c_73022, c_109])).
% 50.47/36.93  tff(c_50, plain, (![A_57, C_59]: (r2_hidden(k4_tarski(A_57, k1_funct_1(C_59, A_57)), C_59) | ~r2_hidden(A_57, k1_relat_1(C_59)) | ~v1_funct_1(C_59) | ~v1_relat_1(C_59))), inference(cnfTransformation, [status(thm)], [f_98])).
% 50.47/36.93  tff(c_6572, plain, (![A_11902, B_11903]: (r2_hidden(k4_tarski('#skF_6'(A_11902, B_11903), '#skF_5'(A_11902, B_11903)), A_11902) | ~r2_hidden('#skF_6'(A_11902, B_11903), k1_relat_1(A_11902)) | ~v1_funct_1(A_11902) | ~v1_relat_1(A_11902) | r2_hidden('#skF_7'(A_11902, B_11903), B_11903) | k2_relat_1(A_11902)=B_11903 | ~v1_funct_1(A_11902) | ~v1_relat_1(A_11902))), inference(superposition, [status(thm), theory('equality')], [c_6564, c_50])).
% 50.47/36.93  tff(c_75209, plain, (![B_57769]: (r2_hidden(k4_tarski('#skF_6'('#skF_10', k1_xboole_0), '#skF_5'('#skF_10', B_57769)), '#skF_10') | ~r2_hidden('#skF_6'('#skF_10', k1_xboole_0), k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | r2_hidden('#skF_7'('#skF_10', k1_xboole_0), k1_xboole_0) | k2_relat_1('#skF_10')=k1_xboole_0 | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | k1_xboole_0!=B_57769 | k1_xboole_0!=B_57769)), inference(superposition, [status(thm), theory('equality')], [c_75186, c_6572])).
% 50.47/36.93  tff(c_75570, plain, (![B_57769]: (r2_hidden(k4_tarski('#skF_9', '#skF_5'('#skF_10', B_57769)), '#skF_10') | r2_hidden('#skF_7'('#skF_10', k1_xboole_0), k1_xboole_0) | k2_relat_1('#skF_10')=k1_xboole_0 | k1_xboole_0!=B_57769)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_62, c_60, c_275, c_6397, c_6397, c_75209])).
% 50.47/36.93  tff(c_75688, plain, (![B_58474]: (r2_hidden(k4_tarski('#skF_9', '#skF_5'('#skF_10', B_58474)), '#skF_10') | k1_xboole_0!=B_58474)), inference(negUnitSimplification, [status(thm)], [c_109, c_135, c_75570])).
% 50.47/36.93  tff(c_52, plain, (![C_59, A_57, B_58]: (k1_funct_1(C_59, A_57)=B_58 | ~r2_hidden(k4_tarski(A_57, B_58), C_59) | ~v1_funct_1(C_59) | ~v1_relat_1(C_59))), inference(cnfTransformation, [status(thm)], [f_98])).
% 50.47/36.93  tff(c_75698, plain, (![B_58474]: (k1_funct_1('#skF_10', '#skF_9')='#skF_5'('#skF_10', B_58474) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | k1_xboole_0!=B_58474)), inference(resolution, [status(thm)], [c_75688, c_52])).
% 50.47/36.93  tff(c_76155, plain, (![B_58474]: ('#skF_5'('#skF_10', k1_xboole_0)='#skF_5'('#skF_10', B_58474) | k1_xboole_0!=B_58474)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_55758, c_75698])).
% 50.47/36.93  tff(c_76163, plain, (![B_58709]: ('#skF_5'('#skF_10', k1_xboole_0)='#skF_5'('#skF_10', B_58709) | k1_xboole_0!=B_58709)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_55758, c_75698])).
% 50.47/36.93  tff(c_76222, plain, (![B_58709, B_58474]: ('#skF_5'('#skF_10', B_58709)='#skF_5'('#skF_10', B_58474) | k1_xboole_0!=B_58709 | k1_xboole_0!=B_58474)), inference(superposition, [status(thm), theory('equality')], [c_76155, c_76163])).
% 50.47/36.93  tff(c_212471, plain, ('#skF_5'('#skF_10', k1_xboole_0)='#skF_4'('#skF_9', '#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_184798, c_76222])).
% 50.47/36.93  tff(c_16, plain, (![A_6, B_7]: (r2_hidden('#skF_3'(A_6, B_7), A_6) | k1_xboole_0=A_6 | k1_tarski(B_7)=A_6)), inference(cnfTransformation, [status(thm)], [f_46])).
% 50.47/36.93  tff(c_184374, plain, (![B_7]: ('#skF_3'(k2_relat_1('#skF_10'), B_7)='#skF_5'('#skF_10', k1_xboole_0) | k2_relat_1('#skF_10')=k1_xboole_0 | k2_relat_1('#skF_10')=k1_tarski(B_7))), inference(resolution, [status(thm)], [c_16, c_184143])).
% 50.47/36.93  tff(c_184416, plain, (![B_7]: ('#skF_3'(k2_relat_1('#skF_10'), B_7)='#skF_5'('#skF_10', k1_xboole_0) | k2_relat_1('#skF_10')=k1_tarski(B_7))), inference(negUnitSimplification, [status(thm)], [c_109, c_184374])).
% 50.47/36.93  tff(c_218464, plain, (![B_183429]: ('#skF_3'(k2_relat_1('#skF_10'), B_183429)='#skF_4'('#skF_9', '#skF_10') | k2_relat_1('#skF_10')=k1_tarski(B_183429))), inference(demodulation, [status(thm), theory('equality')], [c_212471, c_184416])).
% 50.47/36.93  tff(c_218490, plain, (![B_183429]: (B_183429!='#skF_4'('#skF_9', '#skF_10') | k2_relat_1('#skF_10')=k1_xboole_0 | k2_relat_1('#skF_10')=k1_tarski(B_183429) | k2_relat_1('#skF_10')=k1_tarski(B_183429))), inference(superposition, [status(thm), theory('equality')], [c_218464, c_14])).
% 50.47/36.93  tff(c_237035, plain, (k1_tarski('#skF_4'('#skF_9', '#skF_10'))=k2_relat_1('#skF_10')), inference(negUnitSimplification, [status(thm)], [c_109, c_218490])).
% 50.47/36.93  tff(c_184759, plain, ('#skF_5'('#skF_10', k1_xboole_0)='#skF_4'('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_269, c_184417])).
% 50.47/36.93  tff(c_56, plain, (k1_tarski(k1_funct_1('#skF_10', '#skF_9'))!=k2_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_107])).
% 50.47/36.93  tff(c_55776, plain, (k1_tarski('#skF_5'('#skF_10', k1_xboole_0))!=k2_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_55758, c_56])).
% 50.47/36.93  tff(c_184797, plain, (k1_tarski('#skF_4'('#skF_9', '#skF_10'))!=k2_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_184759, c_55776])).
% 50.47/36.93  tff(c_237040, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_237035, c_184797])).
% 50.47/36.93  tff(c_237041, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_108])).
% 50.47/36.93  tff(c_237044, plain, (k1_relat_1('#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_237041, c_103])).
% 50.47/36.93  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 50.47/36.93  tff(c_237049, plain, (k1_relat_1('#skF_10')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_237041, c_237041, c_26])).
% 50.47/36.93  tff(c_237060, plain, $false, inference(negUnitSimplification, [status(thm)], [c_237044, c_237049])).
% 50.47/36.93  tff(c_237061, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_102])).
% 50.47/36.93  tff(c_237065, plain, (![A_11, B_12]: (k2_xboole_0(k1_tarski(A_11), B_12)!='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_237061, c_20])).
% 50.47/36.93  tff(c_237131, plain, (![A_187892]: (~r2_hidden(A_187892, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_237117, c_237065])).
% 50.47/36.93  tff(c_237062, plain, (k1_relat_1('#skF_10')=k1_xboole_0), inference(splitRight, [status(thm)], [c_102])).
% 50.47/36.93  tff(c_237072, plain, (k1_relat_1('#skF_10')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_237061, c_237062])).
% 50.47/36.93  tff(c_75, plain, (![C_60]: (r2_hidden(C_60, k1_tarski(C_60)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 50.47/36.93  tff(c_78, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_75])).
% 50.47/36.93  tff(c_237074, plain, (r2_hidden('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_237072, c_78])).
% 50.47/36.93  tff(c_237133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_237131, c_237074])).
% 50.47/36.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 50.47/36.93  
% 50.47/36.93  Inference rules
% 50.47/36.93  ----------------------
% 50.47/36.93  #Ref     : 27
% 50.47/36.93  #Sup     : 35309
% 50.47/36.93  #Fact    : 7
% 50.47/36.93  #Define  : 0
% 50.47/36.93  #Split   : 32
% 50.47/36.93  #Chain   : 0
% 50.47/36.93  #Close   : 0
% 50.47/36.93  
% 50.47/36.93  Ordering : KBO
% 50.47/36.93  
% 50.47/36.93  Simplification rules
% 50.47/36.93  ----------------------
% 50.47/36.93  #Subsume      : 8770
% 50.47/36.93  #Demod        : 3300
% 50.47/36.93  #Tautology    : 3584
% 50.47/36.93  #SimpNegUnit  : 625
% 50.47/36.93  #BackRed      : 131
% 50.47/36.93  
% 50.47/36.93  #Partial instantiations: 117879
% 50.47/36.93  #Strategies tried      : 1
% 50.47/36.93  
% 50.47/36.93  Timing (in seconds)
% 50.47/36.93  ----------------------
% 50.47/36.93  Preprocessing        : 0.34
% 50.47/36.93  Parsing              : 0.17
% 50.47/36.93  CNF conversion       : 0.03
% 50.47/36.93  Main loop            : 35.75
% 50.47/36.93  Inferencing          : 4.34
% 50.47/36.93  Reduction            : 5.92
% 50.47/36.93  Demodulation         : 3.88
% 50.47/36.93  BG Simplification    : 0.69
% 50.47/36.93  Subsumption          : 23.53
% 50.47/36.93  Abstraction          : 0.79
% 50.47/36.93  MUC search           : 0.00
% 50.47/36.93  Cooper               : 0.00
% 50.47/36.93  Total                : 36.14
% 50.47/36.93  Index Insertion      : 0.00
% 50.47/36.93  Index Deletion       : 0.00
% 50.47/36.93  Index Matching       : 0.00
% 50.47/36.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
