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
% DateTime   : Thu Dec  3 09:52:47 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 187 expanded)
%              Number of leaves         :   30 (  77 expanded)
%              Depth                    :   13
%              Number of atoms          :  121 ( 325 expanded)
%              Number of equality atoms :   55 ( 146 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_68,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_51,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_76,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_60,plain,(
    ! [A_26] : k2_tarski(A_26,A_26) = k1_tarski(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_691,plain,(
    ! [A_119,B_120,C_121] :
      ( r1_tarski(k2_tarski(A_119,B_120),C_121)
      | ~ r2_hidden(B_120,C_121)
      | ~ r2_hidden(A_119,C_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_851,plain,(
    ! [A_143,C_144] :
      ( r1_tarski(k1_tarski(A_143),C_144)
      | ~ r2_hidden(A_143,C_144)
      | ~ r2_hidden(A_143,C_144) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_691])).

tff(c_28,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,B_10) = k1_xboole_0
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_866,plain,(
    ! [A_143,C_144] :
      ( k4_xboole_0(k1_tarski(A_143),C_144) = k1_xboole_0
      | ~ r2_hidden(A_143,C_144) ) ),
    inference(resolution,[status(thm)],[c_851,c_28])).

tff(c_74,plain,(
    k1_tarski('#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_78,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_26,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | k4_xboole_0(A_9,B_10) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_352,plain,(
    ! [B_81,A_82] :
      ( B_81 = A_82
      | ~ r1_tarski(B_81,A_82)
      | ~ r1_tarski(A_82,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_740,plain,(
    ! [B_131,A_132] :
      ( B_131 = A_132
      | ~ r1_tarski(B_131,A_132)
      | k4_xboole_0(A_132,B_131) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_352])).

tff(c_1071,plain,(
    ! [B_165,A_166] :
      ( B_165 = A_166
      | k4_xboole_0(B_165,A_166) != k1_xboole_0
      | k4_xboole_0(A_166,B_165) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_740])).

tff(c_1081,plain,
    ( k1_tarski('#skF_6') = '#skF_5'
    | k4_xboole_0(k1_tarski('#skF_6'),'#skF_5') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_1071])).

tff(c_1093,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_5') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1081])).

tff(c_1101,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_866,c_1093])).

tff(c_38,plain,(
    ! [A_17] : k4_xboole_0(k1_xboole_0,A_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1384,plain,(
    ! [A_190,B_191,C_192] :
      ( r2_hidden('#skF_1'(A_190,B_191,C_192),A_190)
      | r2_hidden('#skF_2'(A_190,B_191,C_192),C_192)
      | k4_xboole_0(A_190,B_191) = C_192 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_34,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_206,plain,(
    ! [A_63,C_64,B_65] :
      ( r2_hidden(A_63,C_64)
      | ~ r1_tarski(k2_tarski(A_63,B_65),C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_221,plain,(
    ! [A_66,C_67] :
      ( r2_hidden(A_66,C_67)
      | ~ r1_tarski(k1_tarski(A_66),C_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_206])).

tff(c_548,plain,(
    ! [A_96,B_97] :
      ( r2_hidden(A_96,B_97)
      | k4_xboole_0(k1_tarski(A_96),B_97) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_221])).

tff(c_563,plain,(
    ! [A_98] :
      ( r2_hidden(A_98,k1_xboole_0)
      | k1_tarski(A_98) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_548])).

tff(c_24,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_149,plain,(
    ! [A_53,B_54] :
      ( k4_xboole_0(A_53,B_54) = k1_xboole_0
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_157,plain,(
    ! [B_8] : k4_xboole_0(B_8,B_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_149])).

tff(c_233,plain,(
    ! [D_68,A_69,B_70] :
      ( r2_hidden(D_68,A_69)
      | ~ r2_hidden(D_68,k4_xboole_0(A_69,B_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_236,plain,(
    ! [D_68,B_8] :
      ( r2_hidden(D_68,B_8)
      | ~ r2_hidden(D_68,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_233])).

tff(c_568,plain,(
    ! [A_98,B_8] :
      ( r2_hidden(A_98,B_8)
      | k1_tarski(A_98) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_563,c_236])).

tff(c_192,plain,(
    ! [D_58,B_59,A_60] :
      ( ~ r2_hidden(D_58,B_59)
      | ~ r2_hidden(D_58,k4_xboole_0(A_60,B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_201,plain,(
    ! [D_58,A_14] :
      ( ~ r2_hidden(D_58,k1_xboole_0)
      | ~ r2_hidden(D_58,A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_192])).

tff(c_613,plain,(
    ! [A_104,A_105] :
      ( ~ r2_hidden(A_104,A_105)
      | k1_tarski(A_104) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_563,c_201])).

tff(c_626,plain,(
    ! [A_98] : k1_tarski(A_98) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_568,c_613])).

tff(c_867,plain,(
    ! [A_145,C_146] :
      ( k4_xboole_0(k1_tarski(A_145),C_146) = k1_xboole_0
      | ~ r2_hidden(A_145,C_146) ) ),
    inference(resolution,[status(thm)],[c_851,c_28])).

tff(c_904,plain,(
    ! [A_145] :
      ( k1_tarski(A_145) = k1_xboole_0
      | ~ r2_hidden(A_145,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_867,c_34])).

tff(c_931,plain,(
    ! [A_145] : ~ r2_hidden(A_145,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_626,c_904])).

tff(c_1405,plain,(
    ! [B_191,C_192] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_191,C_192),C_192)
      | k4_xboole_0(k1_xboole_0,B_191) = C_192 ) ),
    inference(resolution,[status(thm)],[c_1384,c_931])).

tff(c_1500,plain,(
    ! [B_194,C_195] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_194,C_195),C_195)
      | k1_xboole_0 = C_195 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1405])).

tff(c_121,plain,(
    ! [A_45] : k2_tarski(A_45,A_45) = k1_tarski(A_45) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_46,plain,(
    ! [D_25,B_21] : r2_hidden(D_25,k2_tarski(D_25,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_127,plain,(
    ! [A_45] : r2_hidden(A_45,k1_tarski(A_45)) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_46])).

tff(c_631,plain,(
    ! [D_107,A_108,B_109] :
      ( r2_hidden(D_107,k4_xboole_0(A_108,B_109))
      | r2_hidden(D_107,B_109)
      | ~ r2_hidden(D_107,A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_646,plain,(
    ! [D_107] :
      ( r2_hidden(D_107,k1_xboole_0)
      | r2_hidden(D_107,k1_tarski('#skF_6'))
      | ~ r2_hidden(D_107,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_631])).

tff(c_594,plain,(
    ! [D_101,B_102,A_103] :
      ( D_101 = B_102
      | D_101 = A_103
      | ~ r2_hidden(D_101,k2_tarski(A_103,B_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_656,plain,(
    ! [D_111,A_112] :
      ( D_111 = A_112
      | D_111 = A_112
      | ~ r2_hidden(D_111,k1_tarski(A_112)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_594])).

tff(c_666,plain,(
    ! [D_113] :
      ( D_113 = '#skF_6'
      | r2_hidden(D_113,k1_xboole_0)
      | ~ r2_hidden(D_113,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_646,c_656])).

tff(c_674,plain,(
    ! [D_116,A_117] :
      ( ~ r2_hidden(D_116,A_117)
      | D_116 = '#skF_6'
      | ~ r2_hidden(D_116,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_666,c_201])).

tff(c_687,plain,(
    ! [A_45] :
      ( A_45 = '#skF_6'
      | ~ r2_hidden(A_45,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_127,c_674])).

tff(c_1521,plain,(
    ! [B_194] :
      ( '#skF_2'(k1_xboole_0,B_194,'#skF_5') = '#skF_6'
      | k1_xboole_0 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_1500,c_687])).

tff(c_1562,plain,(
    ! [B_196] : '#skF_2'(k1_xboole_0,B_196,'#skF_5') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1521])).

tff(c_1473,plain,(
    ! [B_191,C_192] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_191,C_192),C_192)
      | k1_xboole_0 = C_192 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1405])).

tff(c_1567,plain,
    ( r2_hidden('#skF_6','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1562,c_1473])).

tff(c_1573,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1101,c_1567])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:54:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.53  
% 3.23/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.54  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 3.23/1.54  
% 3.23/1.54  %Foreground sorts:
% 3.23/1.54  
% 3.23/1.54  
% 3.23/1.54  %Background operators:
% 3.23/1.54  
% 3.23/1.54  
% 3.23/1.54  %Foreground operators:
% 3.23/1.54  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.23/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.23/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.23/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.23/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.23/1.54  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.23/1.54  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.23/1.54  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.23/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.23/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.23/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.23/1.54  tff('#skF_5', type, '#skF_5': $i).
% 3.23/1.54  tff('#skF_6', type, '#skF_6': $i).
% 3.23/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.23/1.54  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.23/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.54  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.23/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.23/1.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.23/1.54  
% 3.39/1.55  tff(f_90, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 3.39/1.55  tff(f_68, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.39/1.55  tff(f_80, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.39/1.55  tff(f_45, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.39/1.55  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.39/1.55  tff(f_55, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 3.39/1.55  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.39/1.55  tff(f_51, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.39/1.55  tff(f_66, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 3.39/1.55  tff(c_76, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.39/1.55  tff(c_60, plain, (![A_26]: (k2_tarski(A_26, A_26)=k1_tarski(A_26))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.39/1.55  tff(c_691, plain, (![A_119, B_120, C_121]: (r1_tarski(k2_tarski(A_119, B_120), C_121) | ~r2_hidden(B_120, C_121) | ~r2_hidden(A_119, C_121))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.39/1.55  tff(c_851, plain, (![A_143, C_144]: (r1_tarski(k1_tarski(A_143), C_144) | ~r2_hidden(A_143, C_144) | ~r2_hidden(A_143, C_144))), inference(superposition, [status(thm), theory('equality')], [c_60, c_691])).
% 3.39/1.55  tff(c_28, plain, (![A_9, B_10]: (k4_xboole_0(A_9, B_10)=k1_xboole_0 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.39/1.55  tff(c_866, plain, (![A_143, C_144]: (k4_xboole_0(k1_tarski(A_143), C_144)=k1_xboole_0 | ~r2_hidden(A_143, C_144))), inference(resolution, [status(thm)], [c_851, c_28])).
% 3.39/1.55  tff(c_74, plain, (k1_tarski('#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.39/1.55  tff(c_78, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.39/1.55  tff(c_26, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | k4_xboole_0(A_9, B_10)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.39/1.55  tff(c_352, plain, (![B_81, A_82]: (B_81=A_82 | ~r1_tarski(B_81, A_82) | ~r1_tarski(A_82, B_81))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.39/1.55  tff(c_740, plain, (![B_131, A_132]: (B_131=A_132 | ~r1_tarski(B_131, A_132) | k4_xboole_0(A_132, B_131)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_352])).
% 3.39/1.55  tff(c_1071, plain, (![B_165, A_166]: (B_165=A_166 | k4_xboole_0(B_165, A_166)!=k1_xboole_0 | k4_xboole_0(A_166, B_165)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_740])).
% 3.39/1.55  tff(c_1081, plain, (k1_tarski('#skF_6')='#skF_5' | k4_xboole_0(k1_tarski('#skF_6'), '#skF_5')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_78, c_1071])).
% 3.39/1.55  tff(c_1093, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_5')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_74, c_1081])).
% 3.39/1.55  tff(c_1101, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_866, c_1093])).
% 3.39/1.55  tff(c_38, plain, (![A_17]: (k4_xboole_0(k1_xboole_0, A_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.39/1.55  tff(c_1384, plain, (![A_190, B_191, C_192]: (r2_hidden('#skF_1'(A_190, B_191, C_192), A_190) | r2_hidden('#skF_2'(A_190, B_191, C_192), C_192) | k4_xboole_0(A_190, B_191)=C_192)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.39/1.55  tff(c_34, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.39/1.55  tff(c_206, plain, (![A_63, C_64, B_65]: (r2_hidden(A_63, C_64) | ~r1_tarski(k2_tarski(A_63, B_65), C_64))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.39/1.55  tff(c_221, plain, (![A_66, C_67]: (r2_hidden(A_66, C_67) | ~r1_tarski(k1_tarski(A_66), C_67))), inference(superposition, [status(thm), theory('equality')], [c_60, c_206])).
% 3.39/1.55  tff(c_548, plain, (![A_96, B_97]: (r2_hidden(A_96, B_97) | k4_xboole_0(k1_tarski(A_96), B_97)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_221])).
% 3.39/1.55  tff(c_563, plain, (![A_98]: (r2_hidden(A_98, k1_xboole_0) | k1_tarski(A_98)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_34, c_548])).
% 3.39/1.55  tff(c_24, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.39/1.55  tff(c_149, plain, (![A_53, B_54]: (k4_xboole_0(A_53, B_54)=k1_xboole_0 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.39/1.55  tff(c_157, plain, (![B_8]: (k4_xboole_0(B_8, B_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_149])).
% 3.39/1.55  tff(c_233, plain, (![D_68, A_69, B_70]: (r2_hidden(D_68, A_69) | ~r2_hidden(D_68, k4_xboole_0(A_69, B_70)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.39/1.55  tff(c_236, plain, (![D_68, B_8]: (r2_hidden(D_68, B_8) | ~r2_hidden(D_68, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_157, c_233])).
% 3.39/1.55  tff(c_568, plain, (![A_98, B_8]: (r2_hidden(A_98, B_8) | k1_tarski(A_98)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_563, c_236])).
% 3.39/1.55  tff(c_192, plain, (![D_58, B_59, A_60]: (~r2_hidden(D_58, B_59) | ~r2_hidden(D_58, k4_xboole_0(A_60, B_59)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.39/1.55  tff(c_201, plain, (![D_58, A_14]: (~r2_hidden(D_58, k1_xboole_0) | ~r2_hidden(D_58, A_14))), inference(superposition, [status(thm), theory('equality')], [c_34, c_192])).
% 3.39/1.55  tff(c_613, plain, (![A_104, A_105]: (~r2_hidden(A_104, A_105) | k1_tarski(A_104)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_563, c_201])).
% 3.39/1.55  tff(c_626, plain, (![A_98]: (k1_tarski(A_98)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_568, c_613])).
% 3.39/1.55  tff(c_867, plain, (![A_145, C_146]: (k4_xboole_0(k1_tarski(A_145), C_146)=k1_xboole_0 | ~r2_hidden(A_145, C_146))), inference(resolution, [status(thm)], [c_851, c_28])).
% 3.39/1.55  tff(c_904, plain, (![A_145]: (k1_tarski(A_145)=k1_xboole_0 | ~r2_hidden(A_145, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_867, c_34])).
% 3.39/1.55  tff(c_931, plain, (![A_145]: (~r2_hidden(A_145, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_626, c_904])).
% 3.39/1.55  tff(c_1405, plain, (![B_191, C_192]: (r2_hidden('#skF_2'(k1_xboole_0, B_191, C_192), C_192) | k4_xboole_0(k1_xboole_0, B_191)=C_192)), inference(resolution, [status(thm)], [c_1384, c_931])).
% 3.39/1.55  tff(c_1500, plain, (![B_194, C_195]: (r2_hidden('#skF_2'(k1_xboole_0, B_194, C_195), C_195) | k1_xboole_0=C_195)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1405])).
% 3.39/1.55  tff(c_121, plain, (![A_45]: (k2_tarski(A_45, A_45)=k1_tarski(A_45))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.39/1.55  tff(c_46, plain, (![D_25, B_21]: (r2_hidden(D_25, k2_tarski(D_25, B_21)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.39/1.55  tff(c_127, plain, (![A_45]: (r2_hidden(A_45, k1_tarski(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_121, c_46])).
% 3.39/1.55  tff(c_631, plain, (![D_107, A_108, B_109]: (r2_hidden(D_107, k4_xboole_0(A_108, B_109)) | r2_hidden(D_107, B_109) | ~r2_hidden(D_107, A_108))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.39/1.55  tff(c_646, plain, (![D_107]: (r2_hidden(D_107, k1_xboole_0) | r2_hidden(D_107, k1_tarski('#skF_6')) | ~r2_hidden(D_107, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_631])).
% 3.39/1.55  tff(c_594, plain, (![D_101, B_102, A_103]: (D_101=B_102 | D_101=A_103 | ~r2_hidden(D_101, k2_tarski(A_103, B_102)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.39/1.55  tff(c_656, plain, (![D_111, A_112]: (D_111=A_112 | D_111=A_112 | ~r2_hidden(D_111, k1_tarski(A_112)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_594])).
% 3.39/1.55  tff(c_666, plain, (![D_113]: (D_113='#skF_6' | r2_hidden(D_113, k1_xboole_0) | ~r2_hidden(D_113, '#skF_5'))), inference(resolution, [status(thm)], [c_646, c_656])).
% 3.39/1.55  tff(c_674, plain, (![D_116, A_117]: (~r2_hidden(D_116, A_117) | D_116='#skF_6' | ~r2_hidden(D_116, '#skF_5'))), inference(resolution, [status(thm)], [c_666, c_201])).
% 3.39/1.55  tff(c_687, plain, (![A_45]: (A_45='#skF_6' | ~r2_hidden(A_45, '#skF_5'))), inference(resolution, [status(thm)], [c_127, c_674])).
% 3.39/1.55  tff(c_1521, plain, (![B_194]: ('#skF_2'(k1_xboole_0, B_194, '#skF_5')='#skF_6' | k1_xboole_0='#skF_5')), inference(resolution, [status(thm)], [c_1500, c_687])).
% 3.39/1.55  tff(c_1562, plain, (![B_196]: ('#skF_2'(k1_xboole_0, B_196, '#skF_5')='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_76, c_1521])).
% 3.39/1.55  tff(c_1473, plain, (![B_191, C_192]: (r2_hidden('#skF_2'(k1_xboole_0, B_191, C_192), C_192) | k1_xboole_0=C_192)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1405])).
% 3.39/1.55  tff(c_1567, plain, (r2_hidden('#skF_6', '#skF_5') | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1562, c_1473])).
% 3.39/1.55  tff(c_1573, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_1101, c_1567])).
% 3.39/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.55  
% 3.39/1.55  Inference rules
% 3.39/1.55  ----------------------
% 3.39/1.55  #Ref     : 0
% 3.39/1.55  #Sup     : 342
% 3.39/1.55  #Fact    : 0
% 3.39/1.55  #Define  : 0
% 3.39/1.55  #Split   : 0
% 3.39/1.55  #Chain   : 0
% 3.39/1.55  #Close   : 0
% 3.39/1.55  
% 3.39/1.55  Ordering : KBO
% 3.39/1.55  
% 3.39/1.55  Simplification rules
% 3.39/1.55  ----------------------
% 3.39/1.55  #Subsume      : 67
% 3.39/1.55  #Demod        : 88
% 3.39/1.55  #Tautology    : 151
% 3.39/1.55  #SimpNegUnit  : 31
% 3.39/1.55  #BackRed      : 4
% 3.39/1.55  
% 3.39/1.55  #Partial instantiations: 0
% 3.39/1.55  #Strategies tried      : 1
% 3.39/1.55  
% 3.39/1.55  Timing (in seconds)
% 3.39/1.55  ----------------------
% 3.39/1.55  Preprocessing        : 0.32
% 3.39/1.55  Parsing              : 0.17
% 3.39/1.55  CNF conversion       : 0.03
% 3.39/1.55  Main loop            : 0.43
% 3.39/1.55  Inferencing          : 0.16
% 3.39/1.55  Reduction            : 0.14
% 3.39/1.56  Demodulation         : 0.09
% 3.39/1.56  BG Simplification    : 0.02
% 3.39/1.56  Subsumption          : 0.08
% 3.39/1.56  Abstraction          : 0.02
% 3.39/1.56  MUC search           : 0.00
% 3.39/1.56  Cooper               : 0.00
% 3.39/1.56  Total                : 0.79
% 3.39/1.56  Index Insertion      : 0.00
% 3.39/1.56  Index Deletion       : 0.00
% 3.39/1.56  Index Matching       : 0.00
% 3.39/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
