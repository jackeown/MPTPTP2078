%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:45 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 666 expanded)
%              Number of leaves         :   26 ( 204 expanded)
%              Depth                    :    9
%              Number of atoms          :  219 (1458 expanded)
%              Number of equality atoms :   87 ( 883 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_1 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_63,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_485,plain,(
    ! [A_141,B_142,C_143] :
      ( ~ r1_xboole_0(A_141,B_142)
      | ~ r2_hidden(C_143,B_142)
      | ~ r2_hidden(C_143,A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_488,plain,(
    ! [C_143] : ~ r2_hidden(C_143,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_485])).

tff(c_44,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_63,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_50,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_61,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_72,plain,(
    ! [A_53,B_54,C_55] :
      ( ~ r1_xboole_0(A_53,B_54)
      | ~ r2_hidden(C_55,B_54)
      | ~ r2_hidden(C_55,A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_75,plain,(
    ! [C_55] : ~ r2_hidden(C_55,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_72])).

tff(c_54,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_65,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_122,plain,(
    ! [A_67,B_68,C_69,D_70] :
      ( r2_hidden(k4_tarski(A_67,B_68),k2_zfmisc_1(C_69,D_70))
      | ~ r2_hidden(B_68,D_70)
      | ~ r2_hidden(A_67,C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_131,plain,(
    ! [A_67,B_68] :
      ( r2_hidden(k4_tarski(A_67,B_68),k1_xboole_0)
      | ~ r2_hidden(B_68,'#skF_12')
      | ~ r2_hidden(A_67,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_122])).

tff(c_134,plain,(
    ! [B_68,A_67] :
      ( ~ r2_hidden(B_68,'#skF_12')
      | ~ r2_hidden(A_67,'#skF_11') ) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_131])).

tff(c_136,plain,(
    ! [A_71] : ~ r2_hidden(A_71,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_148,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_8,c_136])).

tff(c_154,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_148])).

tff(c_156,plain,(
    ! [B_72] : ~ r2_hidden(B_72,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_168,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_8,c_156])).

tff(c_174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_168])).

tff(c_175,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_177,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_175])).

tff(c_180,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_8])).

tff(c_283,plain,(
    ! [A_102,B_103,D_104] :
      ( r2_hidden('#skF_8'(A_102,B_103,k2_zfmisc_1(A_102,B_103),D_104),B_103)
      | ~ r2_hidden(D_104,k2_zfmisc_1(A_102,B_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_183,plain,(
    r1_xboole_0('#skF_10','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_177,c_10])).

tff(c_198,plain,(
    ! [A_79,B_80,C_81] :
      ( ~ r1_xboole_0(A_79,B_80)
      | ~ r2_hidden(C_81,B_80)
      | ~ r2_hidden(C_81,A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_201,plain,(
    ! [C_81] : ~ r2_hidden(C_81,'#skF_10') ),
    inference(resolution,[status(thm)],[c_183,c_198])).

tff(c_322,plain,(
    ! [D_106,A_107] : ~ r2_hidden(D_106,k2_zfmisc_1(A_107,'#skF_10')) ),
    inference(resolution,[status(thm)],[c_283,c_201])).

tff(c_355,plain,(
    ! [A_107] : k2_zfmisc_1(A_107,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_180,c_322])).

tff(c_52,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_64,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_178,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_64])).

tff(c_359,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_355,c_178])).

tff(c_360,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_366,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_8])).

tff(c_436,plain,(
    ! [A_132,B_133,D_134] :
      ( r2_hidden('#skF_7'(A_132,B_133,k2_zfmisc_1(A_132,B_133),D_134),A_132)
      | ~ r2_hidden(D_134,k2_zfmisc_1(A_132,B_133)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_369,plain,(
    r1_xboole_0('#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_360,c_10])).

tff(c_383,plain,(
    ! [A_114,B_115,C_116] :
      ( ~ r1_xboole_0(A_114,B_115)
      | ~ r2_hidden(C_116,B_115)
      | ~ r2_hidden(C_116,A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_386,plain,(
    ! [C_116] : ~ r2_hidden(C_116,'#skF_9') ),
    inference(resolution,[status(thm)],[c_369,c_383])).

tff(c_442,plain,(
    ! [D_135,B_136] : ~ r2_hidden(D_135,k2_zfmisc_1('#skF_9',B_136)) ),
    inference(resolution,[status(thm)],[c_436,c_386])).

tff(c_466,plain,(
    ! [B_136] : k2_zfmisc_1('#skF_9',B_136) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_366,c_442])).

tff(c_364,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_64])).

tff(c_471,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_364])).

tff(c_473,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_541,plain,(
    ! [A_155,B_156,C_157,D_158] :
      ( r2_hidden(k4_tarski(A_155,B_156),k2_zfmisc_1(C_157,D_158))
      | ~ r2_hidden(B_156,D_158)
      | ~ r2_hidden(A_155,C_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_550,plain,(
    ! [A_155,B_156] :
      ( r2_hidden(k4_tarski(A_155,B_156),k1_xboole_0)
      | ~ r2_hidden(B_156,'#skF_10')
      | ~ r2_hidden(A_155,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_473,c_541])).

tff(c_556,plain,(
    ! [B_156,A_155] :
      ( ~ r2_hidden(B_156,'#skF_10')
      | ~ r2_hidden(A_155,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_488,c_550])).

tff(c_573,plain,(
    ! [A_162] : ~ r2_hidden(A_162,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_556])).

tff(c_593,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_8,c_573])).

tff(c_599,plain,(
    '#skF_9' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_63])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_601,plain,(
    '#skF_11' != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_61])).

tff(c_472,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_553,plain,(
    ! [A_155,B_156] :
      ( r2_hidden(k4_tarski(A_155,B_156),k1_xboole_0)
      | ~ r2_hidden(B_156,'#skF_12')
      | ~ r2_hidden(A_155,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_472,c_541])).

tff(c_557,plain,(
    ! [B_156,A_155] :
      ( ~ r2_hidden(B_156,'#skF_12')
      | ~ r2_hidden(A_155,'#skF_11') ) ),
    inference(negUnitSimplification,[status(thm)],[c_488,c_553])).

tff(c_725,plain,(
    ! [A_172] : ~ r2_hidden(A_172,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_557])).

tff(c_745,plain,(
    ! [B_2] : r1_xboole_0('#skF_11',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_725])).

tff(c_12,plain,(
    ! [A_8] :
      ( ~ r1_xboole_0(A_8,A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_754,plain,(
    ! [A_175] :
      ( ~ r1_xboole_0(A_175,A_175)
      | A_175 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_12])).

tff(c_758,plain,(
    '#skF_11' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_745,c_754])).

tff(c_774,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_601,c_758])).

tff(c_776,plain,(
    ! [B_176] : ~ r2_hidden(B_176,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_557])).

tff(c_796,plain,(
    ! [B_2] : r1_xboole_0('#skF_12',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_776])).

tff(c_826,plain,(
    ! [A_182] :
      ( ~ r1_xboole_0(A_182,A_182)
      | A_182 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_12])).

tff(c_830,plain,(
    '#skF_9' = '#skF_12' ),
    inference(resolution,[status(thm)],[c_796,c_826])).

tff(c_846,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_599,c_830])).

tff(c_848,plain,(
    ! [B_183] : ~ r2_hidden(B_183,'#skF_10') ),
    inference(splitRight,[status(thm)],[c_556])).

tff(c_863,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_8,c_848])).

tff(c_869,plain,(
    '#skF_10' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_863,c_63])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_871,plain,(
    '#skF_11' != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_863,c_61])).

tff(c_1056,plain,(
    ! [A_200] : ~ r2_hidden(A_200,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_557])).

tff(c_1077,plain,(
    ! [A_201] : r1_xboole_0(A_201,'#skF_11') ),
    inference(resolution,[status(thm)],[c_4,c_1056])).

tff(c_872,plain,(
    ! [A_8] :
      ( ~ r1_xboole_0(A_8,A_8)
      | A_8 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_863,c_12])).

tff(c_1081,plain,(
    '#skF_11' = '#skF_10' ),
    inference(resolution,[status(thm)],[c_1077,c_872])).

tff(c_1087,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_871,c_1081])).

tff(c_1089,plain,(
    ! [B_202] : ~ r2_hidden(B_202,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_557])).

tff(c_1110,plain,(
    ! [A_203] : r1_xboole_0(A_203,'#skF_12') ),
    inference(resolution,[status(thm)],[c_4,c_1089])).

tff(c_1114,plain,(
    '#skF_10' = '#skF_12' ),
    inference(resolution,[status(thm)],[c_1110,c_872])).

tff(c_1120,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_869,c_1114])).

tff(c_1122,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1123,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1122,c_8])).

tff(c_1324,plain,(
    ! [A_262,B_263,D_264] :
      ( r2_hidden('#skF_8'(A_262,B_263,k2_zfmisc_1(A_262,B_263),D_264),B_263)
      | ~ r2_hidden(D_264,k2_zfmisc_1(A_262,B_263)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1126,plain,(
    r1_xboole_0('#skF_12','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1122,c_1122,c_10])).

tff(c_1265,plain,(
    ! [A_241,B_242,C_243] :
      ( ~ r1_xboole_0(A_241,B_242)
      | ~ r2_hidden(C_243,B_242)
      | ~ r2_hidden(C_243,A_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1268,plain,(
    ! [C_243] : ~ r2_hidden(C_243,'#skF_12') ),
    inference(resolution,[status(thm)],[c_1126,c_1265])).

tff(c_1389,plain,(
    ! [D_268,A_269] : ~ r2_hidden(D_268,k2_zfmisc_1(A_269,'#skF_12')) ),
    inference(resolution,[status(thm)],[c_1324,c_1268])).

tff(c_1422,plain,(
    ! [A_269] : k2_zfmisc_1(A_269,'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_1123,c_1389])).

tff(c_1204,plain,(
    ! [A_228,B_229,D_230] :
      ( r2_hidden('#skF_7'(A_228,B_229,k2_zfmisc_1(A_228,B_229),D_230),A_228)
      | ~ r2_hidden(D_230,k2_zfmisc_1(A_228,B_229)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1151,plain,(
    ! [A_210,B_211,C_212] :
      ( ~ r1_xboole_0(A_210,B_211)
      | ~ r2_hidden(C_212,B_211)
      | ~ r2_hidden(C_212,A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1154,plain,(
    ! [C_212] : ~ r2_hidden(C_212,'#skF_12') ),
    inference(resolution,[status(thm)],[c_1126,c_1151])).

tff(c_1216,plain,(
    ! [D_234,B_235] : ~ r2_hidden(D_234,k2_zfmisc_1('#skF_12',B_235)) ),
    inference(resolution,[status(thm)],[c_1204,c_1154])).

tff(c_1246,plain,(
    ! [B_235] : k2_zfmisc_1('#skF_12',B_235) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_1123,c_1216])).

tff(c_46,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1139,plain,
    ( '#skF_10' = '#skF_12'
    | '#skF_9' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1122,c_1122,c_1122,c_46])).

tff(c_1140,plain,(
    '#skF_9' = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_1139])).

tff(c_1121,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1131,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1122,c_1121])).

tff(c_1141,plain,(
    k2_zfmisc_1('#skF_12','#skF_10') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1140,c_1131])).

tff(c_1250,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1246,c_1141])).

tff(c_1251,plain,(
    '#skF_10' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_1139])).

tff(c_1253,plain,(
    k2_zfmisc_1('#skF_9','#skF_12') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1251,c_1131])).

tff(c_1444,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1422,c_1253])).

tff(c_1446,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1445,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1453,plain,
    ( '#skF_11' = '#skF_9'
    | '#skF_11' = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1446,c_1446,c_1445])).

tff(c_1454,plain,(
    '#skF_11' = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_1453])).

tff(c_1456,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1454,c_1446])).

tff(c_1476,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1456,c_8])).

tff(c_1535,plain,(
    ! [A_297,B_298,D_299] :
      ( r2_hidden('#skF_8'(A_297,B_298,k2_zfmisc_1(A_297,B_298),D_299),B_298)
      | ~ r2_hidden(D_299,k2_zfmisc_1(A_297,B_298)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1448,plain,(
    r1_xboole_0('#skF_11','#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1446,c_1446,c_10])).

tff(c_1455,plain,(
    r1_xboole_0('#skF_10','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1454,c_1454,c_1448])).

tff(c_1482,plain,(
    ! [A_279,B_280,C_281] :
      ( ~ r1_xboole_0(A_279,B_280)
      | ~ r2_hidden(C_281,B_280)
      | ~ r2_hidden(C_281,A_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1485,plain,(
    ! [C_281] : ~ r2_hidden(C_281,'#skF_10') ),
    inference(resolution,[status(thm)],[c_1455,c_1482])).

tff(c_1541,plain,(
    ! [D_300,A_301] : ~ r2_hidden(D_300,k2_zfmisc_1(A_301,'#skF_10')) ),
    inference(resolution,[status(thm)],[c_1535,c_1485])).

tff(c_1566,plain,(
    ! [A_301] : k2_zfmisc_1(A_301,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_1476,c_1541])).

tff(c_48,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1474,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1456,c_1454,c_1456,c_48])).

tff(c_1581,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1566,c_1474])).

tff(c_1582,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1453])).

tff(c_1585,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1582,c_1446])).

tff(c_1614,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1585,c_8])).

tff(c_1734,plain,(
    ! [A_335,B_336,D_337] :
      ( r2_hidden('#skF_7'(A_335,B_336,k2_zfmisc_1(A_335,B_336),D_337),A_335)
      | ~ r2_hidden(D_337,k2_zfmisc_1(A_335,B_336)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1584,plain,(
    r1_xboole_0('#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1582,c_1582,c_1448])).

tff(c_1624,plain,(
    ! [A_311,B_312,C_313] :
      ( ~ r1_xboole_0(A_311,B_312)
      | ~ r2_hidden(C_313,B_312)
      | ~ r2_hidden(C_313,A_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1627,plain,(
    ! [C_313] : ~ r2_hidden(C_313,'#skF_9') ),
    inference(resolution,[status(thm)],[c_1584,c_1624])).

tff(c_1744,plain,(
    ! [D_338,B_339] : ~ r2_hidden(D_338,k2_zfmisc_1('#skF_9',B_339)) ),
    inference(resolution,[status(thm)],[c_1734,c_1627])).

tff(c_1777,plain,(
    ! [B_339] : k2_zfmisc_1('#skF_9',B_339) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1614,c_1744])).

tff(c_1591,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1582,c_48])).

tff(c_1592,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_1591])).

tff(c_1598,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1585,c_1592])).

tff(c_1599,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1591])).

tff(c_1606,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1585,c_1599])).

tff(c_1781,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1777,c_1606])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:31:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.48  
% 2.92/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.49  %$ r2_hidden > r1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_1 > #skF_12
% 2.92/1.49  
% 2.92/1.49  %Foreground sorts:
% 2.92/1.49  
% 2.92/1.49  
% 2.92/1.49  %Background operators:
% 2.92/1.49  
% 2.92/1.49  
% 2.92/1.49  %Foreground operators:
% 2.92/1.49  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.92/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.92/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.92/1.49  tff('#skF_11', type, '#skF_11': $i).
% 2.92/1.49  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.92/1.49  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.92/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.92/1.49  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.92/1.49  tff('#skF_10', type, '#skF_10': $i).
% 2.92/1.49  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 2.92/1.49  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.92/1.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.92/1.49  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 2.92/1.49  tff('#skF_9', type, '#skF_9': $i).
% 2.92/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.92/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.92/1.49  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.92/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.92/1.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.92/1.49  tff('#skF_12', type, '#skF_12': $i).
% 2.92/1.49  
% 3.05/1.51  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.05/1.51  tff(f_63, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 3.05/1.51  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.05/1.51  tff(f_88, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.05/1.51  tff(f_81, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.05/1.51  tff(f_75, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 3.05/1.51  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.05/1.51  tff(c_10, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.05/1.51  tff(c_485, plain, (![A_141, B_142, C_143]: (~r1_xboole_0(A_141, B_142) | ~r2_hidden(C_143, B_142) | ~r2_hidden(C_143, A_141))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.05/1.51  tff(c_488, plain, (![C_143]: (~r2_hidden(C_143, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_485])).
% 3.05/1.51  tff(c_44, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.05/1.51  tff(c_63, plain, (k1_xboole_0!='#skF_12'), inference(splitLeft, [status(thm)], [c_44])).
% 3.05/1.51  tff(c_50, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.05/1.51  tff(c_61, plain, (k1_xboole_0!='#skF_11'), inference(splitLeft, [status(thm)], [c_50])).
% 3.05/1.51  tff(c_72, plain, (![A_53, B_54, C_55]: (~r1_xboole_0(A_53, B_54) | ~r2_hidden(C_55, B_54) | ~r2_hidden(C_55, A_53))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.05/1.51  tff(c_75, plain, (![C_55]: (~r2_hidden(C_55, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_72])).
% 3.05/1.51  tff(c_54, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.05/1.51  tff(c_65, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_54])).
% 3.05/1.51  tff(c_122, plain, (![A_67, B_68, C_69, D_70]: (r2_hidden(k4_tarski(A_67, B_68), k2_zfmisc_1(C_69, D_70)) | ~r2_hidden(B_68, D_70) | ~r2_hidden(A_67, C_69))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.05/1.51  tff(c_131, plain, (![A_67, B_68]: (r2_hidden(k4_tarski(A_67, B_68), k1_xboole_0) | ~r2_hidden(B_68, '#skF_12') | ~r2_hidden(A_67, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_122])).
% 3.05/1.51  tff(c_134, plain, (![B_68, A_67]: (~r2_hidden(B_68, '#skF_12') | ~r2_hidden(A_67, '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_75, c_131])).
% 3.05/1.51  tff(c_136, plain, (![A_71]: (~r2_hidden(A_71, '#skF_11'))), inference(splitLeft, [status(thm)], [c_134])).
% 3.05/1.51  tff(c_148, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_8, c_136])).
% 3.05/1.51  tff(c_154, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_148])).
% 3.05/1.51  tff(c_156, plain, (![B_72]: (~r2_hidden(B_72, '#skF_12'))), inference(splitRight, [status(thm)], [c_134])).
% 3.05/1.51  tff(c_168, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_8, c_156])).
% 3.05/1.51  tff(c_174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_168])).
% 3.05/1.51  tff(c_175, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_54])).
% 3.05/1.51  tff(c_177, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_175])).
% 3.05/1.51  tff(c_180, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_177, c_8])).
% 3.05/1.51  tff(c_283, plain, (![A_102, B_103, D_104]: (r2_hidden('#skF_8'(A_102, B_103, k2_zfmisc_1(A_102, B_103), D_104), B_103) | ~r2_hidden(D_104, k2_zfmisc_1(A_102, B_103)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.05/1.51  tff(c_183, plain, (r1_xboole_0('#skF_10', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_177, c_177, c_10])).
% 3.05/1.51  tff(c_198, plain, (![A_79, B_80, C_81]: (~r1_xboole_0(A_79, B_80) | ~r2_hidden(C_81, B_80) | ~r2_hidden(C_81, A_79))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.05/1.51  tff(c_201, plain, (![C_81]: (~r2_hidden(C_81, '#skF_10'))), inference(resolution, [status(thm)], [c_183, c_198])).
% 3.05/1.51  tff(c_322, plain, (![D_106, A_107]: (~r2_hidden(D_106, k2_zfmisc_1(A_107, '#skF_10')))), inference(resolution, [status(thm)], [c_283, c_201])).
% 3.05/1.51  tff(c_355, plain, (![A_107]: (k2_zfmisc_1(A_107, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_180, c_322])).
% 3.05/1.51  tff(c_52, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.05/1.51  tff(c_64, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_52])).
% 3.05/1.51  tff(c_178, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_177, c_64])).
% 3.05/1.51  tff(c_359, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_355, c_178])).
% 3.05/1.51  tff(c_360, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_175])).
% 3.05/1.51  tff(c_366, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_360, c_8])).
% 3.05/1.51  tff(c_436, plain, (![A_132, B_133, D_134]: (r2_hidden('#skF_7'(A_132, B_133, k2_zfmisc_1(A_132, B_133), D_134), A_132) | ~r2_hidden(D_134, k2_zfmisc_1(A_132, B_133)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.05/1.51  tff(c_369, plain, (r1_xboole_0('#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_360, c_360, c_10])).
% 3.05/1.51  tff(c_383, plain, (![A_114, B_115, C_116]: (~r1_xboole_0(A_114, B_115) | ~r2_hidden(C_116, B_115) | ~r2_hidden(C_116, A_114))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.05/1.51  tff(c_386, plain, (![C_116]: (~r2_hidden(C_116, '#skF_9'))), inference(resolution, [status(thm)], [c_369, c_383])).
% 3.05/1.51  tff(c_442, plain, (![D_135, B_136]: (~r2_hidden(D_135, k2_zfmisc_1('#skF_9', B_136)))), inference(resolution, [status(thm)], [c_436, c_386])).
% 3.05/1.51  tff(c_466, plain, (![B_136]: (k2_zfmisc_1('#skF_9', B_136)='#skF_9')), inference(resolution, [status(thm)], [c_366, c_442])).
% 3.05/1.51  tff(c_364, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_360, c_64])).
% 3.05/1.51  tff(c_471, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_466, c_364])).
% 3.05/1.51  tff(c_473, plain, (k2_zfmisc_1('#skF_9', '#skF_10')=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 3.05/1.51  tff(c_541, plain, (![A_155, B_156, C_157, D_158]: (r2_hidden(k4_tarski(A_155, B_156), k2_zfmisc_1(C_157, D_158)) | ~r2_hidden(B_156, D_158) | ~r2_hidden(A_155, C_157))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.05/1.51  tff(c_550, plain, (![A_155, B_156]: (r2_hidden(k4_tarski(A_155, B_156), k1_xboole_0) | ~r2_hidden(B_156, '#skF_10') | ~r2_hidden(A_155, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_473, c_541])).
% 3.05/1.51  tff(c_556, plain, (![B_156, A_155]: (~r2_hidden(B_156, '#skF_10') | ~r2_hidden(A_155, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_488, c_550])).
% 3.05/1.51  tff(c_573, plain, (![A_162]: (~r2_hidden(A_162, '#skF_9'))), inference(splitLeft, [status(thm)], [c_556])).
% 3.05/1.51  tff(c_593, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_8, c_573])).
% 3.05/1.51  tff(c_599, plain, ('#skF_9'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_593, c_63])).
% 3.05/1.51  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.05/1.51  tff(c_601, plain, ('#skF_11'!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_593, c_61])).
% 3.05/1.51  tff(c_472, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 3.05/1.51  tff(c_553, plain, (![A_155, B_156]: (r2_hidden(k4_tarski(A_155, B_156), k1_xboole_0) | ~r2_hidden(B_156, '#skF_12') | ~r2_hidden(A_155, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_472, c_541])).
% 3.05/1.51  tff(c_557, plain, (![B_156, A_155]: (~r2_hidden(B_156, '#skF_12') | ~r2_hidden(A_155, '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_488, c_553])).
% 3.05/1.51  tff(c_725, plain, (![A_172]: (~r2_hidden(A_172, '#skF_11'))), inference(splitLeft, [status(thm)], [c_557])).
% 3.05/1.51  tff(c_745, plain, (![B_2]: (r1_xboole_0('#skF_11', B_2))), inference(resolution, [status(thm)], [c_6, c_725])).
% 3.05/1.51  tff(c_12, plain, (![A_8]: (~r1_xboole_0(A_8, A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.05/1.51  tff(c_754, plain, (![A_175]: (~r1_xboole_0(A_175, A_175) | A_175='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_593, c_12])).
% 3.05/1.51  tff(c_758, plain, ('#skF_11'='#skF_9'), inference(resolution, [status(thm)], [c_745, c_754])).
% 3.05/1.51  tff(c_774, plain, $false, inference(negUnitSimplification, [status(thm)], [c_601, c_758])).
% 3.05/1.51  tff(c_776, plain, (![B_176]: (~r2_hidden(B_176, '#skF_12'))), inference(splitRight, [status(thm)], [c_557])).
% 3.05/1.51  tff(c_796, plain, (![B_2]: (r1_xboole_0('#skF_12', B_2))), inference(resolution, [status(thm)], [c_6, c_776])).
% 3.05/1.51  tff(c_826, plain, (![A_182]: (~r1_xboole_0(A_182, A_182) | A_182='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_593, c_12])).
% 3.05/1.51  tff(c_830, plain, ('#skF_9'='#skF_12'), inference(resolution, [status(thm)], [c_796, c_826])).
% 3.05/1.51  tff(c_846, plain, $false, inference(negUnitSimplification, [status(thm)], [c_599, c_830])).
% 3.05/1.51  tff(c_848, plain, (![B_183]: (~r2_hidden(B_183, '#skF_10'))), inference(splitRight, [status(thm)], [c_556])).
% 3.05/1.51  tff(c_863, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_8, c_848])).
% 3.05/1.51  tff(c_869, plain, ('#skF_10'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_863, c_63])).
% 3.05/1.51  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.05/1.51  tff(c_871, plain, ('#skF_11'!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_863, c_61])).
% 3.05/1.51  tff(c_1056, plain, (![A_200]: (~r2_hidden(A_200, '#skF_11'))), inference(splitLeft, [status(thm)], [c_557])).
% 3.05/1.51  tff(c_1077, plain, (![A_201]: (r1_xboole_0(A_201, '#skF_11'))), inference(resolution, [status(thm)], [c_4, c_1056])).
% 3.05/1.51  tff(c_872, plain, (![A_8]: (~r1_xboole_0(A_8, A_8) | A_8='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_863, c_12])).
% 3.05/1.51  tff(c_1081, plain, ('#skF_11'='#skF_10'), inference(resolution, [status(thm)], [c_1077, c_872])).
% 3.05/1.51  tff(c_1087, plain, $false, inference(negUnitSimplification, [status(thm)], [c_871, c_1081])).
% 3.05/1.51  tff(c_1089, plain, (![B_202]: (~r2_hidden(B_202, '#skF_12'))), inference(splitRight, [status(thm)], [c_557])).
% 3.05/1.51  tff(c_1110, plain, (![A_203]: (r1_xboole_0(A_203, '#skF_12'))), inference(resolution, [status(thm)], [c_4, c_1089])).
% 3.05/1.51  tff(c_1114, plain, ('#skF_10'='#skF_12'), inference(resolution, [status(thm)], [c_1110, c_872])).
% 3.05/1.51  tff(c_1120, plain, $false, inference(negUnitSimplification, [status(thm)], [c_869, c_1114])).
% 3.05/1.51  tff(c_1122, plain, (k1_xboole_0='#skF_12'), inference(splitRight, [status(thm)], [c_44])).
% 3.05/1.51  tff(c_1123, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_1122, c_8])).
% 3.05/1.51  tff(c_1324, plain, (![A_262, B_263, D_264]: (r2_hidden('#skF_8'(A_262, B_263, k2_zfmisc_1(A_262, B_263), D_264), B_263) | ~r2_hidden(D_264, k2_zfmisc_1(A_262, B_263)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.05/1.51  tff(c_1126, plain, (r1_xboole_0('#skF_12', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_1122, c_1122, c_10])).
% 3.05/1.51  tff(c_1265, plain, (![A_241, B_242, C_243]: (~r1_xboole_0(A_241, B_242) | ~r2_hidden(C_243, B_242) | ~r2_hidden(C_243, A_241))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.05/1.51  tff(c_1268, plain, (![C_243]: (~r2_hidden(C_243, '#skF_12'))), inference(resolution, [status(thm)], [c_1126, c_1265])).
% 3.05/1.51  tff(c_1389, plain, (![D_268, A_269]: (~r2_hidden(D_268, k2_zfmisc_1(A_269, '#skF_12')))), inference(resolution, [status(thm)], [c_1324, c_1268])).
% 3.05/1.51  tff(c_1422, plain, (![A_269]: (k2_zfmisc_1(A_269, '#skF_12')='#skF_12')), inference(resolution, [status(thm)], [c_1123, c_1389])).
% 3.05/1.51  tff(c_1204, plain, (![A_228, B_229, D_230]: (r2_hidden('#skF_7'(A_228, B_229, k2_zfmisc_1(A_228, B_229), D_230), A_228) | ~r2_hidden(D_230, k2_zfmisc_1(A_228, B_229)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.05/1.51  tff(c_1151, plain, (![A_210, B_211, C_212]: (~r1_xboole_0(A_210, B_211) | ~r2_hidden(C_212, B_211) | ~r2_hidden(C_212, A_210))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.05/1.51  tff(c_1154, plain, (![C_212]: (~r2_hidden(C_212, '#skF_12'))), inference(resolution, [status(thm)], [c_1126, c_1151])).
% 3.05/1.51  tff(c_1216, plain, (![D_234, B_235]: (~r2_hidden(D_234, k2_zfmisc_1('#skF_12', B_235)))), inference(resolution, [status(thm)], [c_1204, c_1154])).
% 3.05/1.51  tff(c_1246, plain, (![B_235]: (k2_zfmisc_1('#skF_12', B_235)='#skF_12')), inference(resolution, [status(thm)], [c_1123, c_1216])).
% 3.05/1.51  tff(c_46, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.05/1.51  tff(c_1139, plain, ('#skF_10'='#skF_12' | '#skF_9'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_1122, c_1122, c_1122, c_46])).
% 3.05/1.51  tff(c_1140, plain, ('#skF_9'='#skF_12'), inference(splitLeft, [status(thm)], [c_1139])).
% 3.05/1.51  tff(c_1121, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_44])).
% 3.05/1.51  tff(c_1131, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_1122, c_1121])).
% 3.05/1.51  tff(c_1141, plain, (k2_zfmisc_1('#skF_12', '#skF_10')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_1140, c_1131])).
% 3.05/1.51  tff(c_1250, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1246, c_1141])).
% 3.05/1.51  tff(c_1251, plain, ('#skF_10'='#skF_12'), inference(splitRight, [status(thm)], [c_1139])).
% 3.05/1.51  tff(c_1253, plain, (k2_zfmisc_1('#skF_9', '#skF_12')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_1251, c_1131])).
% 3.05/1.51  tff(c_1444, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1422, c_1253])).
% 3.05/1.51  tff(c_1446, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_50])).
% 3.05/1.51  tff(c_1445, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_50])).
% 3.05/1.51  tff(c_1453, plain, ('#skF_11'='#skF_9' | '#skF_11'='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1446, c_1446, c_1445])).
% 3.05/1.51  tff(c_1454, plain, ('#skF_11'='#skF_10'), inference(splitLeft, [status(thm)], [c_1453])).
% 3.05/1.51  tff(c_1456, plain, (k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1454, c_1446])).
% 3.05/1.51  tff(c_1476, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1456, c_8])).
% 3.05/1.51  tff(c_1535, plain, (![A_297, B_298, D_299]: (r2_hidden('#skF_8'(A_297, B_298, k2_zfmisc_1(A_297, B_298), D_299), B_298) | ~r2_hidden(D_299, k2_zfmisc_1(A_297, B_298)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.05/1.51  tff(c_1448, plain, (r1_xboole_0('#skF_11', '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_1446, c_1446, c_10])).
% 3.05/1.51  tff(c_1455, plain, (r1_xboole_0('#skF_10', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1454, c_1454, c_1448])).
% 3.05/1.51  tff(c_1482, plain, (![A_279, B_280, C_281]: (~r1_xboole_0(A_279, B_280) | ~r2_hidden(C_281, B_280) | ~r2_hidden(C_281, A_279))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.05/1.51  tff(c_1485, plain, (![C_281]: (~r2_hidden(C_281, '#skF_10'))), inference(resolution, [status(thm)], [c_1455, c_1482])).
% 3.05/1.51  tff(c_1541, plain, (![D_300, A_301]: (~r2_hidden(D_300, k2_zfmisc_1(A_301, '#skF_10')))), inference(resolution, [status(thm)], [c_1535, c_1485])).
% 3.05/1.51  tff(c_1566, plain, (![A_301]: (k2_zfmisc_1(A_301, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_1476, c_1541])).
% 3.05/1.51  tff(c_48, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.05/1.51  tff(c_1474, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1456, c_1454, c_1456, c_48])).
% 3.05/1.51  tff(c_1581, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1566, c_1474])).
% 3.05/1.51  tff(c_1582, plain, ('#skF_11'='#skF_9'), inference(splitRight, [status(thm)], [c_1453])).
% 3.05/1.51  tff(c_1585, plain, (k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1582, c_1446])).
% 3.05/1.51  tff(c_1614, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1585, c_8])).
% 3.05/1.51  tff(c_1734, plain, (![A_335, B_336, D_337]: (r2_hidden('#skF_7'(A_335, B_336, k2_zfmisc_1(A_335, B_336), D_337), A_335) | ~r2_hidden(D_337, k2_zfmisc_1(A_335, B_336)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.05/1.51  tff(c_1584, plain, (r1_xboole_0('#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1582, c_1582, c_1448])).
% 3.05/1.51  tff(c_1624, plain, (![A_311, B_312, C_313]: (~r1_xboole_0(A_311, B_312) | ~r2_hidden(C_313, B_312) | ~r2_hidden(C_313, A_311))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.05/1.51  tff(c_1627, plain, (![C_313]: (~r2_hidden(C_313, '#skF_9'))), inference(resolution, [status(thm)], [c_1584, c_1624])).
% 3.05/1.51  tff(c_1744, plain, (![D_338, B_339]: (~r2_hidden(D_338, k2_zfmisc_1('#skF_9', B_339)))), inference(resolution, [status(thm)], [c_1734, c_1627])).
% 3.05/1.51  tff(c_1777, plain, (![B_339]: (k2_zfmisc_1('#skF_9', B_339)='#skF_9')), inference(resolution, [status(thm)], [c_1614, c_1744])).
% 3.05/1.51  tff(c_1591, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1582, c_48])).
% 3.05/1.51  tff(c_1592, plain, (k1_xboole_0!='#skF_9'), inference(splitLeft, [status(thm)], [c_1591])).
% 3.05/1.51  tff(c_1598, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1585, c_1592])).
% 3.05/1.51  tff(c_1599, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_1591])).
% 3.05/1.51  tff(c_1606, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1585, c_1599])).
% 3.05/1.51  tff(c_1781, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1777, c_1606])).
% 3.05/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.51  
% 3.05/1.51  Inference rules
% 3.05/1.51  ----------------------
% 3.05/1.51  #Ref     : 0
% 3.05/1.51  #Sup     : 338
% 3.05/1.51  #Fact    : 0
% 3.05/1.51  #Define  : 0
% 3.05/1.51  #Split   : 13
% 3.05/1.51  #Chain   : 0
% 3.05/1.51  #Close   : 0
% 3.05/1.51  
% 3.05/1.51  Ordering : KBO
% 3.05/1.51  
% 3.05/1.51  Simplification rules
% 3.05/1.51  ----------------------
% 3.05/1.51  #Subsume      : 117
% 3.05/1.51  #Demod        : 161
% 3.05/1.51  #Tautology    : 119
% 3.05/1.51  #SimpNegUnit  : 32
% 3.05/1.51  #BackRed      : 61
% 3.05/1.51  
% 3.05/1.51  #Partial instantiations: 0
% 3.05/1.51  #Strategies tried      : 1
% 3.05/1.51  
% 3.05/1.51  Timing (in seconds)
% 3.05/1.51  ----------------------
% 3.05/1.51  Preprocessing        : 0.31
% 3.05/1.51  Parsing              : 0.15
% 3.05/1.51  CNF conversion       : 0.03
% 3.05/1.51  Main loop            : 0.41
% 3.05/1.51  Inferencing          : 0.16
% 3.05/1.51  Reduction            : 0.11
% 3.05/1.51  Demodulation         : 0.07
% 3.05/1.51  BG Simplification    : 0.02
% 3.05/1.51  Subsumption          : 0.07
% 3.05/1.51  Abstraction          : 0.02
% 3.05/1.51  MUC search           : 0.00
% 3.05/1.51  Cooper               : 0.00
% 3.05/1.51  Total                : 0.77
% 3.05/1.51  Index Insertion      : 0.00
% 3.05/1.51  Index Deletion       : 0.00
% 3.05/1.51  Index Matching       : 0.00
% 3.05/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
