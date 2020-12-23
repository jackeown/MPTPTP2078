%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:10 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 243 expanded)
%              Number of leaves         :   36 (  97 expanded)
%              Depth                    :   15
%              Number of atoms          :  163 ( 659 expanded)
%              Number of equality atoms :   92 ( 360 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_8 > #skF_3 > #skF_10 > #skF_7 > #skF_2 > #skF_1 > #skF_9 > #skF_5 > #skF_4

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

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_79,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_110,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_61,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_92,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(c_56,plain,(
    ! [A_36] : v1_relat_1('#skF_8'(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_54,plain,(
    ! [A_36] : v1_funct_1('#skF_8'(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_52,plain,(
    ! [A_36] : k1_relat_1('#skF_8'(A_36)) = A_36 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_68,plain,
    ( k1_xboole_0 = '#skF_11'
    | k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_90,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_44,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1151,plain,(
    ! [A_200,B_201] :
      ( r2_hidden(k4_tarski('#skF_4'(A_200,B_201),'#skF_5'(A_200,B_201)),A_200)
      | r2_hidden('#skF_6'(A_200,B_201),B_201)
      | k1_relat_1(A_200) = B_201 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_24,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_119,plain,(
    ! [A_58,B_59] : ~ r2_hidden(A_58,k2_zfmisc_1(A_58,B_59)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_125,plain,(
    ! [A_12] : ~ r2_hidden(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_119])).

tff(c_1172,plain,(
    ! [B_201] :
      ( r2_hidden('#skF_6'(k1_xboole_0,B_201),B_201)
      | k1_relat_1(k1_xboole_0) = B_201 ) ),
    inference(resolution,[status(thm)],[c_1151,c_125])).

tff(c_1348,plain,(
    ! [B_209] :
      ( r2_hidden('#skF_6'(k1_xboole_0,B_209),B_209)
      | k1_xboole_0 = B_209 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1172])).

tff(c_60,plain,(
    ! [A_42,B_46] :
      ( k1_relat_1('#skF_9'(A_42,B_46)) = A_42
      | k1_xboole_0 = A_42 ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_62,plain,(
    ! [A_42,B_46] :
      ( v1_funct_1('#skF_9'(A_42,B_46))
      | k1_xboole_0 = A_42 ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_64,plain,(
    ! [A_42,B_46] :
      ( v1_relat_1('#skF_9'(A_42,B_46))
      | k1_xboole_0 = A_42 ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_169,plain,(
    ! [A_75,B_76] :
      ( r2_hidden('#skF_1'(A_75,B_76),A_75)
      | r1_tarski(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [C_11,A_7] :
      ( C_11 = A_7
      | ~ r2_hidden(C_11,k1_tarski(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_273,plain,(
    ! [A_97,B_98] :
      ( '#skF_1'(k1_tarski(A_97),B_98) = A_97
      | r1_tarski(k1_tarski(A_97),B_98) ) ),
    inference(resolution,[status(thm)],[c_169,c_10])).

tff(c_148,plain,(
    ! [A_71,B_72] :
      ( k2_relat_1('#skF_9'(A_71,B_72)) = k1_tarski(B_72)
      | k1_xboole_0 = A_71 ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_66,plain,(
    ! [C_49] :
      ( ~ r1_tarski(k2_relat_1(C_49),'#skF_10')
      | k1_relat_1(C_49) != '#skF_11'
      | ~ v1_funct_1(C_49)
      | ~ v1_relat_1(C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_154,plain,(
    ! [B_72,A_71] :
      ( ~ r1_tarski(k1_tarski(B_72),'#skF_10')
      | k1_relat_1('#skF_9'(A_71,B_72)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_71,B_72))
      | ~ v1_relat_1('#skF_9'(A_71,B_72))
      | k1_xboole_0 = A_71 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_66])).

tff(c_282,plain,(
    ! [A_99,A_100] :
      ( k1_relat_1('#skF_9'(A_99,A_100)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_99,A_100))
      | ~ v1_relat_1('#skF_9'(A_99,A_100))
      | k1_xboole_0 = A_99
      | '#skF_1'(k1_tarski(A_100),'#skF_10') = A_100 ) ),
    inference(resolution,[status(thm)],[c_273,c_154])).

tff(c_607,plain,(
    ! [A_137,B_138] :
      ( k1_relat_1('#skF_9'(A_137,B_138)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_137,B_138))
      | '#skF_1'(k1_tarski(B_138),'#skF_10') = B_138
      | k1_xboole_0 = A_137 ) ),
    inference(resolution,[status(thm)],[c_64,c_282])).

tff(c_768,plain,(
    ! [A_156,B_157] :
      ( k1_relat_1('#skF_9'(A_156,B_157)) != '#skF_11'
      | '#skF_1'(k1_tarski(B_157),'#skF_10') = B_157
      | k1_xboole_0 = A_156 ) ),
    inference(resolution,[status(thm)],[c_62,c_607])).

tff(c_771,plain,(
    ! [A_42,B_46] :
      ( A_42 != '#skF_11'
      | '#skF_1'(k1_tarski(B_46),'#skF_10') = B_46
      | k1_xboole_0 = A_42
      | k1_xboole_0 = A_42 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_768])).

tff(c_773,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_771])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_210,plain,(
    ! [A_84] :
      ( k2_relat_1(A_84) = k1_xboole_0
      | k1_relat_1(A_84) != k1_xboole_0
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_216,plain,(
    ! [A_36] :
      ( k2_relat_1('#skF_8'(A_36)) = k1_xboole_0
      | k1_relat_1('#skF_8'(A_36)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_56,c_210])).

tff(c_221,plain,(
    ! [A_85] :
      ( k2_relat_1('#skF_8'(A_85)) = k1_xboole_0
      | k1_xboole_0 != A_85 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_216])).

tff(c_230,plain,(
    ! [A_85] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_10')
      | k1_relat_1('#skF_8'(A_85)) != '#skF_11'
      | ~ v1_funct_1('#skF_8'(A_85))
      | ~ v1_relat_1('#skF_8'(A_85))
      | k1_xboole_0 != A_85 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_66])).

tff(c_237,plain,(
    ! [A_85] :
      ( A_85 != '#skF_11'
      | k1_xboole_0 != A_85 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_8,c_230])).

tff(c_242,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_237])).

tff(c_806,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_773,c_242])).

tff(c_809,plain,(
    ! [B_158] : '#skF_1'(k1_tarski(B_158),'#skF_10') = B_158 ),
    inference(splitRight,[status(thm)],[c_771])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_840,plain,(
    ! [B_159] :
      ( ~ r2_hidden(B_159,'#skF_10')
      | r1_tarski(k1_tarski(B_159),'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_809,c_4])).

tff(c_926,plain,(
    ! [A_166,B_167] :
      ( k1_relat_1('#skF_9'(A_166,B_167)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_166,B_167))
      | ~ v1_relat_1('#skF_9'(A_166,B_167))
      | k1_xboole_0 = A_166
      | ~ r2_hidden(B_167,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_840,c_154])).

tff(c_1059,plain,(
    ! [A_193,B_194] :
      ( k1_relat_1('#skF_9'(A_193,B_194)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_193,B_194))
      | ~ r2_hidden(B_194,'#skF_10')
      | k1_xboole_0 = A_193 ) ),
    inference(resolution,[status(thm)],[c_64,c_926])).

tff(c_1064,plain,(
    ! [A_195,B_196] :
      ( k1_relat_1('#skF_9'(A_195,B_196)) != '#skF_11'
      | ~ r2_hidden(B_196,'#skF_10')
      | k1_xboole_0 = A_195 ) ),
    inference(resolution,[status(thm)],[c_62,c_1059])).

tff(c_1067,plain,(
    ! [A_42,B_46] :
      ( A_42 != '#skF_11'
      | ~ r2_hidden(B_46,'#skF_10')
      | k1_xboole_0 = A_42
      | k1_xboole_0 = A_42 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_1064])).

tff(c_1068,plain,(
    ! [B_46] : ~ r2_hidden(B_46,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_1067])).

tff(c_1364,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_1348,c_1068])).

tff(c_1381,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_1364])).

tff(c_1383,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_1067])).

tff(c_1416,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1383,c_242])).

tff(c_1418,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_1417,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_1426,plain,(
    '#skF_11' = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1418,c_1417])).

tff(c_1419,plain,(
    ! [A_6] : r1_tarski('#skF_11',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1417,c_8])).

tff(c_1452,plain,(
    ! [A_6] : r1_tarski('#skF_10',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1426,c_1419])).

tff(c_48,plain,(
    ! [A_35] :
      ( k2_relat_1(A_35) = k1_xboole_0
      | k1_relat_1(A_35) != k1_xboole_0
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1564,plain,(
    ! [A_236] :
      ( k2_relat_1(A_236) = '#skF_10'
      | k1_relat_1(A_236) != '#skF_10'
      | ~ v1_relat_1(A_236) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1418,c_1418,c_48])).

tff(c_1570,plain,(
    ! [A_36] :
      ( k2_relat_1('#skF_8'(A_36)) = '#skF_10'
      | k1_relat_1('#skF_8'(A_36)) != '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_56,c_1564])).

tff(c_1575,plain,(
    ! [A_237] :
      ( k2_relat_1('#skF_8'(A_237)) = '#skF_10'
      | A_237 != '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1570])).

tff(c_1445,plain,(
    ! [C_49] :
      ( ~ r1_tarski(k2_relat_1(C_49),'#skF_10')
      | k1_relat_1(C_49) != '#skF_10'
      | ~ v1_funct_1(C_49)
      | ~ v1_relat_1(C_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1426,c_66])).

tff(c_1584,plain,(
    ! [A_237] :
      ( ~ r1_tarski('#skF_10','#skF_10')
      | k1_relat_1('#skF_8'(A_237)) != '#skF_10'
      | ~ v1_funct_1('#skF_8'(A_237))
      | ~ v1_relat_1('#skF_8'(A_237))
      | A_237 != '#skF_10' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1575,c_1445])).

tff(c_1591,plain,(
    ! [A_237] : A_237 != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_1452,c_1584])).

tff(c_26,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1462,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_10',B_13) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1418,c_1418,c_26])).

tff(c_1608,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1591,c_1462])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:03:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.52  
% 3.32/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.52  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_8 > #skF_3 > #skF_10 > #skF_7 > #skF_2 > #skF_1 > #skF_9 > #skF_5 > #skF_4
% 3.32/1.52  
% 3.32/1.52  %Foreground sorts:
% 3.32/1.52  
% 3.32/1.52  
% 3.32/1.52  %Background operators:
% 3.32/1.52  
% 3.32/1.52  
% 3.32/1.52  %Foreground operators:
% 3.32/1.52  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.32/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.32/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.32/1.52  tff('#skF_11', type, '#skF_11': $i).
% 3.32/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.32/1.52  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.32/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.32/1.52  tff('#skF_8', type, '#skF_8': $i > $i).
% 3.32/1.52  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.32/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.32/1.52  tff('#skF_10', type, '#skF_10': $i).
% 3.32/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.32/1.52  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 3.32/1.52  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.32/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.32/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.32/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.32/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.32/1.52  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 3.32/1.52  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.32/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.32/1.52  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.32/1.52  
% 3.49/1.54  tff(f_79, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 3.49/1.54  tff(f_110, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_1)).
% 3.49/1.54  tff(f_61, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.49/1.54  tff(f_58, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 3.49/1.54  tff(f_47, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.49/1.54  tff(f_50, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.49/1.54  tff(f_92, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_funct_1)).
% 3.49/1.54  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.49/1.54  tff(f_41, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.49/1.54  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.49/1.54  tff(f_67, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 3.49/1.54  tff(c_56, plain, (![A_36]: (v1_relat_1('#skF_8'(A_36)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.49/1.54  tff(c_54, plain, (![A_36]: (v1_funct_1('#skF_8'(A_36)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.49/1.54  tff(c_52, plain, (![A_36]: (k1_relat_1('#skF_8'(A_36))=A_36)), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.49/1.54  tff(c_68, plain, (k1_xboole_0='#skF_11' | k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.49/1.54  tff(c_90, plain, (k1_xboole_0!='#skF_10'), inference(splitLeft, [status(thm)], [c_68])).
% 3.49/1.54  tff(c_44, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.49/1.54  tff(c_1151, plain, (![A_200, B_201]: (r2_hidden(k4_tarski('#skF_4'(A_200, B_201), '#skF_5'(A_200, B_201)), A_200) | r2_hidden('#skF_6'(A_200, B_201), B_201) | k1_relat_1(A_200)=B_201)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.49/1.54  tff(c_24, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.49/1.54  tff(c_119, plain, (![A_58, B_59]: (~r2_hidden(A_58, k2_zfmisc_1(A_58, B_59)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.49/1.54  tff(c_125, plain, (![A_12]: (~r2_hidden(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_119])).
% 3.49/1.54  tff(c_1172, plain, (![B_201]: (r2_hidden('#skF_6'(k1_xboole_0, B_201), B_201) | k1_relat_1(k1_xboole_0)=B_201)), inference(resolution, [status(thm)], [c_1151, c_125])).
% 3.49/1.54  tff(c_1348, plain, (![B_209]: (r2_hidden('#skF_6'(k1_xboole_0, B_209), B_209) | k1_xboole_0=B_209)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1172])).
% 3.49/1.54  tff(c_60, plain, (![A_42, B_46]: (k1_relat_1('#skF_9'(A_42, B_46))=A_42 | k1_xboole_0=A_42)), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.49/1.54  tff(c_62, plain, (![A_42, B_46]: (v1_funct_1('#skF_9'(A_42, B_46)) | k1_xboole_0=A_42)), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.49/1.54  tff(c_64, plain, (![A_42, B_46]: (v1_relat_1('#skF_9'(A_42, B_46)) | k1_xboole_0=A_42)), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.49/1.54  tff(c_169, plain, (![A_75, B_76]: (r2_hidden('#skF_1'(A_75, B_76), A_75) | r1_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.49/1.54  tff(c_10, plain, (![C_11, A_7]: (C_11=A_7 | ~r2_hidden(C_11, k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.49/1.54  tff(c_273, plain, (![A_97, B_98]: ('#skF_1'(k1_tarski(A_97), B_98)=A_97 | r1_tarski(k1_tarski(A_97), B_98))), inference(resolution, [status(thm)], [c_169, c_10])).
% 3.49/1.54  tff(c_148, plain, (![A_71, B_72]: (k2_relat_1('#skF_9'(A_71, B_72))=k1_tarski(B_72) | k1_xboole_0=A_71)), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.49/1.54  tff(c_66, plain, (![C_49]: (~r1_tarski(k2_relat_1(C_49), '#skF_10') | k1_relat_1(C_49)!='#skF_11' | ~v1_funct_1(C_49) | ~v1_relat_1(C_49))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.49/1.54  tff(c_154, plain, (![B_72, A_71]: (~r1_tarski(k1_tarski(B_72), '#skF_10') | k1_relat_1('#skF_9'(A_71, B_72))!='#skF_11' | ~v1_funct_1('#skF_9'(A_71, B_72)) | ~v1_relat_1('#skF_9'(A_71, B_72)) | k1_xboole_0=A_71)), inference(superposition, [status(thm), theory('equality')], [c_148, c_66])).
% 3.49/1.54  tff(c_282, plain, (![A_99, A_100]: (k1_relat_1('#skF_9'(A_99, A_100))!='#skF_11' | ~v1_funct_1('#skF_9'(A_99, A_100)) | ~v1_relat_1('#skF_9'(A_99, A_100)) | k1_xboole_0=A_99 | '#skF_1'(k1_tarski(A_100), '#skF_10')=A_100)), inference(resolution, [status(thm)], [c_273, c_154])).
% 3.49/1.54  tff(c_607, plain, (![A_137, B_138]: (k1_relat_1('#skF_9'(A_137, B_138))!='#skF_11' | ~v1_funct_1('#skF_9'(A_137, B_138)) | '#skF_1'(k1_tarski(B_138), '#skF_10')=B_138 | k1_xboole_0=A_137)), inference(resolution, [status(thm)], [c_64, c_282])).
% 3.49/1.54  tff(c_768, plain, (![A_156, B_157]: (k1_relat_1('#skF_9'(A_156, B_157))!='#skF_11' | '#skF_1'(k1_tarski(B_157), '#skF_10')=B_157 | k1_xboole_0=A_156)), inference(resolution, [status(thm)], [c_62, c_607])).
% 3.49/1.54  tff(c_771, plain, (![A_42, B_46]: (A_42!='#skF_11' | '#skF_1'(k1_tarski(B_46), '#skF_10')=B_46 | k1_xboole_0=A_42 | k1_xboole_0=A_42)), inference(superposition, [status(thm), theory('equality')], [c_60, c_768])).
% 3.49/1.54  tff(c_773, plain, (k1_xboole_0='#skF_11'), inference(splitLeft, [status(thm)], [c_771])).
% 3.49/1.54  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.49/1.54  tff(c_210, plain, (![A_84]: (k2_relat_1(A_84)=k1_xboole_0 | k1_relat_1(A_84)!=k1_xboole_0 | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.49/1.54  tff(c_216, plain, (![A_36]: (k2_relat_1('#skF_8'(A_36))=k1_xboole_0 | k1_relat_1('#skF_8'(A_36))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_56, c_210])).
% 3.49/1.54  tff(c_221, plain, (![A_85]: (k2_relat_1('#skF_8'(A_85))=k1_xboole_0 | k1_xboole_0!=A_85)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_216])).
% 3.49/1.54  tff(c_230, plain, (![A_85]: (~r1_tarski(k1_xboole_0, '#skF_10') | k1_relat_1('#skF_8'(A_85))!='#skF_11' | ~v1_funct_1('#skF_8'(A_85)) | ~v1_relat_1('#skF_8'(A_85)) | k1_xboole_0!=A_85)), inference(superposition, [status(thm), theory('equality')], [c_221, c_66])).
% 3.49/1.54  tff(c_237, plain, (![A_85]: (A_85!='#skF_11' | k1_xboole_0!=A_85)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_8, c_230])).
% 3.49/1.54  tff(c_242, plain, (k1_xboole_0!='#skF_11'), inference(reflexivity, [status(thm), theory('equality')], [c_237])).
% 3.49/1.54  tff(c_806, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_773, c_242])).
% 3.49/1.54  tff(c_809, plain, (![B_158]: ('#skF_1'(k1_tarski(B_158), '#skF_10')=B_158)), inference(splitRight, [status(thm)], [c_771])).
% 3.49/1.54  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.49/1.54  tff(c_840, plain, (![B_159]: (~r2_hidden(B_159, '#skF_10') | r1_tarski(k1_tarski(B_159), '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_809, c_4])).
% 3.49/1.54  tff(c_926, plain, (![A_166, B_167]: (k1_relat_1('#skF_9'(A_166, B_167))!='#skF_11' | ~v1_funct_1('#skF_9'(A_166, B_167)) | ~v1_relat_1('#skF_9'(A_166, B_167)) | k1_xboole_0=A_166 | ~r2_hidden(B_167, '#skF_10'))), inference(resolution, [status(thm)], [c_840, c_154])).
% 3.49/1.54  tff(c_1059, plain, (![A_193, B_194]: (k1_relat_1('#skF_9'(A_193, B_194))!='#skF_11' | ~v1_funct_1('#skF_9'(A_193, B_194)) | ~r2_hidden(B_194, '#skF_10') | k1_xboole_0=A_193)), inference(resolution, [status(thm)], [c_64, c_926])).
% 3.49/1.54  tff(c_1064, plain, (![A_195, B_196]: (k1_relat_1('#skF_9'(A_195, B_196))!='#skF_11' | ~r2_hidden(B_196, '#skF_10') | k1_xboole_0=A_195)), inference(resolution, [status(thm)], [c_62, c_1059])).
% 3.49/1.54  tff(c_1067, plain, (![A_42, B_46]: (A_42!='#skF_11' | ~r2_hidden(B_46, '#skF_10') | k1_xboole_0=A_42 | k1_xboole_0=A_42)), inference(superposition, [status(thm), theory('equality')], [c_60, c_1064])).
% 3.49/1.54  tff(c_1068, plain, (![B_46]: (~r2_hidden(B_46, '#skF_10'))), inference(splitLeft, [status(thm)], [c_1067])).
% 3.49/1.54  tff(c_1364, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_1348, c_1068])).
% 3.49/1.54  tff(c_1381, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_1364])).
% 3.49/1.54  tff(c_1383, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_1067])).
% 3.49/1.54  tff(c_1416, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1383, c_242])).
% 3.49/1.54  tff(c_1418, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_68])).
% 3.49/1.54  tff(c_1417, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_68])).
% 3.49/1.54  tff(c_1426, plain, ('#skF_11'='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1418, c_1417])).
% 3.49/1.54  tff(c_1419, plain, (![A_6]: (r1_tarski('#skF_11', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_1417, c_8])).
% 3.49/1.54  tff(c_1452, plain, (![A_6]: (r1_tarski('#skF_10', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_1426, c_1419])).
% 3.49/1.54  tff(c_48, plain, (![A_35]: (k2_relat_1(A_35)=k1_xboole_0 | k1_relat_1(A_35)!=k1_xboole_0 | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.49/1.54  tff(c_1564, plain, (![A_236]: (k2_relat_1(A_236)='#skF_10' | k1_relat_1(A_236)!='#skF_10' | ~v1_relat_1(A_236))), inference(demodulation, [status(thm), theory('equality')], [c_1418, c_1418, c_48])).
% 3.49/1.54  tff(c_1570, plain, (![A_36]: (k2_relat_1('#skF_8'(A_36))='#skF_10' | k1_relat_1('#skF_8'(A_36))!='#skF_10')), inference(resolution, [status(thm)], [c_56, c_1564])).
% 3.49/1.54  tff(c_1575, plain, (![A_237]: (k2_relat_1('#skF_8'(A_237))='#skF_10' | A_237!='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1570])).
% 3.49/1.54  tff(c_1445, plain, (![C_49]: (~r1_tarski(k2_relat_1(C_49), '#skF_10') | k1_relat_1(C_49)!='#skF_10' | ~v1_funct_1(C_49) | ~v1_relat_1(C_49))), inference(demodulation, [status(thm), theory('equality')], [c_1426, c_66])).
% 3.49/1.54  tff(c_1584, plain, (![A_237]: (~r1_tarski('#skF_10', '#skF_10') | k1_relat_1('#skF_8'(A_237))!='#skF_10' | ~v1_funct_1('#skF_8'(A_237)) | ~v1_relat_1('#skF_8'(A_237)) | A_237!='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_1575, c_1445])).
% 3.49/1.54  tff(c_1591, plain, (![A_237]: (A_237!='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_1452, c_1584])).
% 3.49/1.54  tff(c_26, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.49/1.54  tff(c_1462, plain, (![B_13]: (k2_zfmisc_1('#skF_10', B_13)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1418, c_1418, c_26])).
% 3.49/1.54  tff(c_1608, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1591, c_1462])).
% 3.49/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.54  
% 3.49/1.54  Inference rules
% 3.49/1.54  ----------------------
% 3.49/1.54  #Ref     : 1
% 3.49/1.54  #Sup     : 315
% 3.49/1.54  #Fact    : 0
% 3.49/1.54  #Define  : 0
% 3.49/1.54  #Split   : 6
% 3.49/1.54  #Chain   : 0
% 3.49/1.54  #Close   : 0
% 3.49/1.54  
% 3.49/1.54  Ordering : KBO
% 3.49/1.54  
% 3.49/1.54  Simplification rules
% 3.49/1.54  ----------------------
% 3.49/1.54  #Subsume      : 62
% 3.49/1.54  #Demod        : 212
% 3.49/1.54  #Tautology    : 158
% 3.49/1.54  #SimpNegUnit  : 31
% 3.49/1.54  #BackRed      : 77
% 3.49/1.54  
% 3.49/1.54  #Partial instantiations: 0
% 3.49/1.54  #Strategies tried      : 1
% 3.49/1.54  
% 3.49/1.54  Timing (in seconds)
% 3.49/1.54  ----------------------
% 3.49/1.54  Preprocessing        : 0.31
% 3.49/1.54  Parsing              : 0.16
% 3.55/1.54  CNF conversion       : 0.03
% 3.55/1.54  Main loop            : 0.46
% 3.55/1.54  Inferencing          : 0.17
% 3.55/1.54  Reduction            : 0.14
% 3.55/1.54  Demodulation         : 0.10
% 3.55/1.54  BG Simplification    : 0.03
% 3.55/1.54  Subsumption          : 0.08
% 3.55/1.54  Abstraction          : 0.02
% 3.55/1.54  MUC search           : 0.00
% 3.55/1.54  Cooper               : 0.00
% 3.55/1.54  Total                : 0.80
% 3.55/1.54  Index Insertion      : 0.00
% 3.55/1.54  Index Deletion       : 0.00
% 3.55/1.54  Index Matching       : 0.00
% 3.55/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
