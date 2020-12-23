%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:08 EST 2020

% Result     : Theorem 5.44s
% Output     : CNFRefutation 5.66s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 144 expanded)
%              Number of leaves         :   19 (  56 expanded)
%              Depth                    :   13
%              Number of atoms          :  105 ( 376 expanded)
%              Number of equality atoms :   43 ( 123 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_42,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_40,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_47,negated_conjecture,(
    ~ ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_515,plain,(
    ! [B_81,C_82] :
      ( r2_hidden('#skF_2'(B_81,B_81,C_82),C_82)
      | k2_xboole_0(B_81,B_81) = C_82
      | r2_hidden('#skF_1'(B_81,B_81,C_82),B_81) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_18])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_562,plain,(
    ! [B_83] :
      ( r2_hidden('#skF_2'(B_83,B_83,B_83),B_83)
      | k2_xboole_0(B_83,B_83) = B_83 ) ),
    inference(resolution,[status(thm)],[c_515,c_16])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_312,plain,(
    ! [B_71,C_72] :
      ( ~ r2_hidden('#skF_2'(B_71,B_71,C_72),B_71)
      | k2_xboole_0(B_71,B_71) = C_72
      | r2_hidden('#skF_1'(B_71,B_71,C_72),B_71) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_14])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_335,plain,(
    ! [B_71] :
      ( ~ r2_hidden('#skF_2'(B_71,B_71,B_71),B_71)
      | k2_xboole_0(B_71,B_71) = B_71 ) ),
    inference(resolution,[status(thm)],[c_312,c_8])).

tff(c_581,plain,(
    ! [B_83] : k2_xboole_0(B_83,B_83) = B_83 ),
    inference(resolution,[status(thm)],[c_562,c_335])).

tff(c_26,plain,(
    ! [A_13,B_14,C_15] : k2_xboole_0(k1_tarski(A_13),k2_tarski(B_14,C_15)) = k1_enumset1(A_13,B_14,C_15) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_24,plain,(
    ! [A_11,B_12] : k2_xboole_0(k1_tarski(A_11),k1_tarski(B_12)) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_415,plain,(
    ! [A_76,B_77,C_78] :
      ( r2_hidden('#skF_1'(A_76,B_77,C_78),B_77)
      | r2_hidden('#skF_1'(A_76,B_77,C_78),A_76)
      | r2_hidden('#skF_2'(A_76,B_77,C_78),C_78)
      | k2_xboole_0(A_76,B_77) = C_78 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_477,plain,(
    ! [A_76,B_77] :
      ( r2_hidden('#skF_1'(A_76,B_77,B_77),A_76)
      | r2_hidden('#skF_2'(A_76,B_77,B_77),B_77)
      | k2_xboole_0(A_76,B_77) = B_77 ) ),
    inference(resolution,[status(thm)],[c_415,c_16])).

tff(c_599,plain,(
    ! [A_84,B_85,C_86] :
      ( r2_hidden('#skF_1'(A_84,B_85,C_86),B_85)
      | r2_hidden('#skF_1'(A_84,B_85,C_86),A_84)
      | ~ r2_hidden('#skF_2'(A_84,B_85,C_86),B_85)
      | k2_xboole_0(A_84,B_85) = C_86 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_823,plain,(
    ! [A_94,B_95] :
      ( r2_hidden('#skF_1'(A_94,B_95,B_95),A_94)
      | ~ r2_hidden('#skF_2'(A_94,B_95,B_95),B_95)
      | k2_xboole_0(A_94,B_95) = B_95 ) ),
    inference(resolution,[status(thm)],[c_599,c_8])).

tff(c_846,plain,(
    ! [A_76,B_77] :
      ( r2_hidden('#skF_1'(A_76,B_77,B_77),A_76)
      | k2_xboole_0(A_76,B_77) = B_77 ) ),
    inference(resolution,[status(thm)],[c_477,c_823])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( ~ r2_hidden(D_6,A_1)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_147,plain,(
    ! [A_55,B_56,C_57] :
      ( ~ r2_hidden('#skF_1'(A_55,B_56,C_57),C_57)
      | r2_hidden('#skF_2'(A_55,B_56,C_57),C_57)
      | k2_xboole_0(A_55,B_56) = C_57 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1375,plain,(
    ! [A_128,B_129,A_130,B_131] :
      ( r2_hidden('#skF_2'(A_128,B_129,k2_xboole_0(A_130,B_131)),k2_xboole_0(A_130,B_131))
      | k2_xboole_0(A_130,B_131) = k2_xboole_0(A_128,B_129)
      | ~ r2_hidden('#skF_1'(A_128,B_129,k2_xboole_0(A_130,B_131)),B_131) ) ),
    inference(resolution,[status(thm)],[c_4,c_147])).

tff(c_216,plain,(
    ! [A_65,B_66,C_67] :
      ( ~ r2_hidden('#skF_1'(A_65,B_66,C_67),C_67)
      | ~ r2_hidden('#skF_2'(A_65,B_66,C_67),B_66)
      | k2_xboole_0(A_65,B_66) = C_67 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_239,plain,(
    ! [A_65,B_66,A_1,B_2] :
      ( ~ r2_hidden('#skF_2'(A_65,B_66,k2_xboole_0(A_1,B_2)),B_66)
      | k2_xboole_0(A_65,B_66) = k2_xboole_0(A_1,B_2)
      | ~ r2_hidden('#skF_1'(A_65,B_66,k2_xboole_0(A_1,B_2)),B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_216])).

tff(c_1424,plain,(
    ! [A_132,A_133,B_134] :
      ( k2_xboole_0(A_132,k2_xboole_0(A_133,B_134)) = k2_xboole_0(A_133,B_134)
      | ~ r2_hidden('#skF_1'(A_132,k2_xboole_0(A_133,B_134),k2_xboole_0(A_133,B_134)),B_134) ) ),
    inference(resolution,[status(thm)],[c_1375,c_239])).

tff(c_1448,plain,(
    ! [A_132,B_83] :
      ( k2_xboole_0(A_132,k2_xboole_0(B_83,B_83)) = k2_xboole_0(B_83,B_83)
      | ~ r2_hidden('#skF_1'(A_132,k2_xboole_0(B_83,B_83),B_83),B_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_581,c_1424])).

tff(c_1691,plain,(
    ! [A_141,B_142] :
      ( k2_xboole_0(A_141,B_142) = B_142
      | ~ r2_hidden('#skF_1'(A_141,B_142,B_142),B_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_581,c_581,c_581,c_1448])).

tff(c_3276,plain,(
    ! [A_178,A_179,B_180] :
      ( k2_xboole_0(A_178,k2_xboole_0(A_179,B_180)) = k2_xboole_0(A_179,B_180)
      | ~ r2_hidden('#skF_1'(A_178,k2_xboole_0(A_179,B_180),k2_xboole_0(A_179,B_180)),A_179) ) ),
    inference(resolution,[status(thm)],[c_6,c_1691])).

tff(c_3567,plain,(
    ! [A_183,B_184] : k2_xboole_0(A_183,k2_xboole_0(A_183,B_184)) = k2_xboole_0(A_183,B_184) ),
    inference(resolution,[status(thm)],[c_846,c_3276])).

tff(c_3688,plain,(
    ! [A_11,B_12] : k2_xboole_0(k1_tarski(A_11),k2_tarski(A_11,B_12)) = k2_xboole_0(k1_tarski(A_11),k1_tarski(B_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_3567])).

tff(c_3842,plain,(
    ! [A_187,B_188] : k2_xboole_0(k1_tarski(A_187),k2_tarski(A_187,B_188)) = k2_tarski(A_187,B_188) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_3688])).

tff(c_917,plain,(
    ! [A_100,B_101] :
      ( r2_hidden('#skF_1'(A_100,B_101,A_100),B_101)
      | r2_hidden('#skF_2'(A_100,B_101,A_100),A_100)
      | k2_xboole_0(A_100,B_101) = A_100 ) ),
    inference(resolution,[status(thm)],[c_415,c_16])).

tff(c_255,plain,(
    ! [A_68,B_69,C_70] :
      ( r2_hidden('#skF_1'(A_68,B_69,C_70),B_69)
      | r2_hidden('#skF_1'(A_68,B_69,C_70),A_68)
      | ~ r2_hidden('#skF_2'(A_68,B_69,C_70),A_68)
      | k2_xboole_0(A_68,B_69) = C_70 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_307,plain,(
    ! [A_68,B_69] :
      ( r2_hidden('#skF_1'(A_68,B_69,A_68),B_69)
      | ~ r2_hidden('#skF_2'(A_68,B_69,A_68),A_68)
      | k2_xboole_0(A_68,B_69) = A_68 ) ),
    inference(resolution,[status(thm)],[c_255,c_12])).

tff(c_963,plain,(
    ! [A_100,B_101] :
      ( r2_hidden('#skF_1'(A_100,B_101,A_100),B_101)
      | k2_xboole_0(A_100,B_101) = A_100 ) ),
    inference(resolution,[status(thm)],[c_917,c_307])).

tff(c_191,plain,(
    ! [A_62,B_63,C_64] :
      ( ~ r2_hidden('#skF_1'(A_62,B_63,C_64),C_64)
      | ~ r2_hidden('#skF_2'(A_62,B_63,C_64),A_62)
      | k2_xboole_0(A_62,B_63) = C_64 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_214,plain,(
    ! [A_62,B_63,A_1,B_2] :
      ( ~ r2_hidden('#skF_2'(A_62,B_63,k2_xboole_0(A_1,B_2)),A_62)
      | k2_xboole_0(A_62,B_63) = k2_xboole_0(A_1,B_2)
      | ~ r2_hidden('#skF_1'(A_62,B_63,k2_xboole_0(A_1,B_2)),B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_191])).

tff(c_3138,plain,(
    ! [A_175,B_176,B_177] :
      ( k2_xboole_0(k2_xboole_0(A_175,B_176),B_177) = k2_xboole_0(A_175,B_176)
      | ~ r2_hidden('#skF_1'(k2_xboole_0(A_175,B_176),B_177,k2_xboole_0(A_175,B_176)),B_176) ) ),
    inference(resolution,[status(thm)],[c_1375,c_214])).

tff(c_3263,plain,(
    ! [A_175,B_101] : k2_xboole_0(k2_xboole_0(A_175,B_101),B_101) = k2_xboole_0(A_175,B_101) ),
    inference(resolution,[status(thm)],[c_963,c_3138])).

tff(c_3851,plain,(
    ! [A_187,B_188] : k2_xboole_0(k2_tarski(A_187,B_188),k2_tarski(A_187,B_188)) = k2_xboole_0(k1_tarski(A_187),k2_tarski(A_187,B_188)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3842,c_3263])).

tff(c_3946,plain,(
    ! [A_187,B_188] : k1_enumset1(A_187,A_187,B_188) = k2_tarski(A_187,B_188) ),
    inference(demodulation,[status(thm),theory(equality)],[c_581,c_26,c_3851])).

tff(c_30,plain,(
    k1_enumset1('#skF_3','#skF_3','#skF_4') != k2_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3974,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3946,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:59:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.44/2.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.66/2.17  
% 5.66/2.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.66/2.17  %$ r2_hidden > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 5.66/2.17  
% 5.66/2.17  %Foreground sorts:
% 5.66/2.17  
% 5.66/2.17  
% 5.66/2.17  %Background operators:
% 5.66/2.17  
% 5.66/2.17  
% 5.66/2.17  %Foreground operators:
% 5.66/2.17  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.66/2.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.66/2.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.66/2.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.66/2.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.66/2.17  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.66/2.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.66/2.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.66/2.17  tff('#skF_3', type, '#skF_3': $i).
% 5.66/2.17  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.66/2.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.66/2.17  tff('#skF_4', type, '#skF_4': $i).
% 5.66/2.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.66/2.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.66/2.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.66/2.17  
% 5.66/2.18  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 5.66/2.18  tff(f_42, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 5.66/2.18  tff(f_40, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 5.66/2.18  tff(f_47, negated_conjecture, ~(![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 5.66/2.18  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k2_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.66/2.18  tff(c_515, plain, (![B_81, C_82]: (r2_hidden('#skF_2'(B_81, B_81, C_82), C_82) | k2_xboole_0(B_81, B_81)=C_82 | r2_hidden('#skF_1'(B_81, B_81, C_82), B_81))), inference(factorization, [status(thm), theory('equality')], [c_18])).
% 5.66/2.18  tff(c_16, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k2_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.66/2.18  tff(c_562, plain, (![B_83]: (r2_hidden('#skF_2'(B_83, B_83, B_83), B_83) | k2_xboole_0(B_83, B_83)=B_83)), inference(resolution, [status(thm)], [c_515, c_16])).
% 5.66/2.18  tff(c_14, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k2_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.66/2.18  tff(c_312, plain, (![B_71, C_72]: (~r2_hidden('#skF_2'(B_71, B_71, C_72), B_71) | k2_xboole_0(B_71, B_71)=C_72 | r2_hidden('#skF_1'(B_71, B_71, C_72), B_71))), inference(factorization, [status(thm), theory('equality')], [c_14])).
% 5.66/2.18  tff(c_8, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | k2_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.66/2.18  tff(c_335, plain, (![B_71]: (~r2_hidden('#skF_2'(B_71, B_71, B_71), B_71) | k2_xboole_0(B_71, B_71)=B_71)), inference(resolution, [status(thm)], [c_312, c_8])).
% 5.66/2.18  tff(c_581, plain, (![B_83]: (k2_xboole_0(B_83, B_83)=B_83)), inference(resolution, [status(thm)], [c_562, c_335])).
% 5.66/2.18  tff(c_26, plain, (![A_13, B_14, C_15]: (k2_xboole_0(k1_tarski(A_13), k2_tarski(B_14, C_15))=k1_enumset1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.66/2.18  tff(c_24, plain, (![A_11, B_12]: (k2_xboole_0(k1_tarski(A_11), k1_tarski(B_12))=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.66/2.18  tff(c_415, plain, (![A_76, B_77, C_78]: (r2_hidden('#skF_1'(A_76, B_77, C_78), B_77) | r2_hidden('#skF_1'(A_76, B_77, C_78), A_76) | r2_hidden('#skF_2'(A_76, B_77, C_78), C_78) | k2_xboole_0(A_76, B_77)=C_78)), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.66/2.18  tff(c_477, plain, (![A_76, B_77]: (r2_hidden('#skF_1'(A_76, B_77, B_77), A_76) | r2_hidden('#skF_2'(A_76, B_77, B_77), B_77) | k2_xboole_0(A_76, B_77)=B_77)), inference(resolution, [status(thm)], [c_415, c_16])).
% 5.66/2.18  tff(c_599, plain, (![A_84, B_85, C_86]: (r2_hidden('#skF_1'(A_84, B_85, C_86), B_85) | r2_hidden('#skF_1'(A_84, B_85, C_86), A_84) | ~r2_hidden('#skF_2'(A_84, B_85, C_86), B_85) | k2_xboole_0(A_84, B_85)=C_86)), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.66/2.18  tff(c_823, plain, (![A_94, B_95]: (r2_hidden('#skF_1'(A_94, B_95, B_95), A_94) | ~r2_hidden('#skF_2'(A_94, B_95, B_95), B_95) | k2_xboole_0(A_94, B_95)=B_95)), inference(resolution, [status(thm)], [c_599, c_8])).
% 5.66/2.18  tff(c_846, plain, (![A_76, B_77]: (r2_hidden('#skF_1'(A_76, B_77, B_77), A_76) | k2_xboole_0(A_76, B_77)=B_77)), inference(resolution, [status(thm)], [c_477, c_823])).
% 5.66/2.18  tff(c_6, plain, (![D_6, A_1, B_2]: (~r2_hidden(D_6, A_1) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.66/2.18  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.66/2.18  tff(c_147, plain, (![A_55, B_56, C_57]: (~r2_hidden('#skF_1'(A_55, B_56, C_57), C_57) | r2_hidden('#skF_2'(A_55, B_56, C_57), C_57) | k2_xboole_0(A_55, B_56)=C_57)), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.66/2.18  tff(c_1375, plain, (![A_128, B_129, A_130, B_131]: (r2_hidden('#skF_2'(A_128, B_129, k2_xboole_0(A_130, B_131)), k2_xboole_0(A_130, B_131)) | k2_xboole_0(A_130, B_131)=k2_xboole_0(A_128, B_129) | ~r2_hidden('#skF_1'(A_128, B_129, k2_xboole_0(A_130, B_131)), B_131))), inference(resolution, [status(thm)], [c_4, c_147])).
% 5.66/2.18  tff(c_216, plain, (![A_65, B_66, C_67]: (~r2_hidden('#skF_1'(A_65, B_66, C_67), C_67) | ~r2_hidden('#skF_2'(A_65, B_66, C_67), B_66) | k2_xboole_0(A_65, B_66)=C_67)), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.66/2.18  tff(c_239, plain, (![A_65, B_66, A_1, B_2]: (~r2_hidden('#skF_2'(A_65, B_66, k2_xboole_0(A_1, B_2)), B_66) | k2_xboole_0(A_65, B_66)=k2_xboole_0(A_1, B_2) | ~r2_hidden('#skF_1'(A_65, B_66, k2_xboole_0(A_1, B_2)), B_2))), inference(resolution, [status(thm)], [c_4, c_216])).
% 5.66/2.18  tff(c_1424, plain, (![A_132, A_133, B_134]: (k2_xboole_0(A_132, k2_xboole_0(A_133, B_134))=k2_xboole_0(A_133, B_134) | ~r2_hidden('#skF_1'(A_132, k2_xboole_0(A_133, B_134), k2_xboole_0(A_133, B_134)), B_134))), inference(resolution, [status(thm)], [c_1375, c_239])).
% 5.66/2.18  tff(c_1448, plain, (![A_132, B_83]: (k2_xboole_0(A_132, k2_xboole_0(B_83, B_83))=k2_xboole_0(B_83, B_83) | ~r2_hidden('#skF_1'(A_132, k2_xboole_0(B_83, B_83), B_83), B_83))), inference(superposition, [status(thm), theory('equality')], [c_581, c_1424])).
% 5.66/2.18  tff(c_1691, plain, (![A_141, B_142]: (k2_xboole_0(A_141, B_142)=B_142 | ~r2_hidden('#skF_1'(A_141, B_142, B_142), B_142))), inference(demodulation, [status(thm), theory('equality')], [c_581, c_581, c_581, c_1448])).
% 5.66/2.18  tff(c_3276, plain, (![A_178, A_179, B_180]: (k2_xboole_0(A_178, k2_xboole_0(A_179, B_180))=k2_xboole_0(A_179, B_180) | ~r2_hidden('#skF_1'(A_178, k2_xboole_0(A_179, B_180), k2_xboole_0(A_179, B_180)), A_179))), inference(resolution, [status(thm)], [c_6, c_1691])).
% 5.66/2.18  tff(c_3567, plain, (![A_183, B_184]: (k2_xboole_0(A_183, k2_xboole_0(A_183, B_184))=k2_xboole_0(A_183, B_184))), inference(resolution, [status(thm)], [c_846, c_3276])).
% 5.66/2.18  tff(c_3688, plain, (![A_11, B_12]: (k2_xboole_0(k1_tarski(A_11), k2_tarski(A_11, B_12))=k2_xboole_0(k1_tarski(A_11), k1_tarski(B_12)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_3567])).
% 5.66/2.18  tff(c_3842, plain, (![A_187, B_188]: (k2_xboole_0(k1_tarski(A_187), k2_tarski(A_187, B_188))=k2_tarski(A_187, B_188))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_3688])).
% 5.66/2.18  tff(c_917, plain, (![A_100, B_101]: (r2_hidden('#skF_1'(A_100, B_101, A_100), B_101) | r2_hidden('#skF_2'(A_100, B_101, A_100), A_100) | k2_xboole_0(A_100, B_101)=A_100)), inference(resolution, [status(thm)], [c_415, c_16])).
% 5.66/2.18  tff(c_255, plain, (![A_68, B_69, C_70]: (r2_hidden('#skF_1'(A_68, B_69, C_70), B_69) | r2_hidden('#skF_1'(A_68, B_69, C_70), A_68) | ~r2_hidden('#skF_2'(A_68, B_69, C_70), A_68) | k2_xboole_0(A_68, B_69)=C_70)), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.66/2.18  tff(c_12, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k2_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.66/2.18  tff(c_307, plain, (![A_68, B_69]: (r2_hidden('#skF_1'(A_68, B_69, A_68), B_69) | ~r2_hidden('#skF_2'(A_68, B_69, A_68), A_68) | k2_xboole_0(A_68, B_69)=A_68)), inference(resolution, [status(thm)], [c_255, c_12])).
% 5.66/2.18  tff(c_963, plain, (![A_100, B_101]: (r2_hidden('#skF_1'(A_100, B_101, A_100), B_101) | k2_xboole_0(A_100, B_101)=A_100)), inference(resolution, [status(thm)], [c_917, c_307])).
% 5.66/2.18  tff(c_191, plain, (![A_62, B_63, C_64]: (~r2_hidden('#skF_1'(A_62, B_63, C_64), C_64) | ~r2_hidden('#skF_2'(A_62, B_63, C_64), A_62) | k2_xboole_0(A_62, B_63)=C_64)), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.66/2.18  tff(c_214, plain, (![A_62, B_63, A_1, B_2]: (~r2_hidden('#skF_2'(A_62, B_63, k2_xboole_0(A_1, B_2)), A_62) | k2_xboole_0(A_62, B_63)=k2_xboole_0(A_1, B_2) | ~r2_hidden('#skF_1'(A_62, B_63, k2_xboole_0(A_1, B_2)), B_2))), inference(resolution, [status(thm)], [c_4, c_191])).
% 5.66/2.18  tff(c_3138, plain, (![A_175, B_176, B_177]: (k2_xboole_0(k2_xboole_0(A_175, B_176), B_177)=k2_xboole_0(A_175, B_176) | ~r2_hidden('#skF_1'(k2_xboole_0(A_175, B_176), B_177, k2_xboole_0(A_175, B_176)), B_176))), inference(resolution, [status(thm)], [c_1375, c_214])).
% 5.66/2.18  tff(c_3263, plain, (![A_175, B_101]: (k2_xboole_0(k2_xboole_0(A_175, B_101), B_101)=k2_xboole_0(A_175, B_101))), inference(resolution, [status(thm)], [c_963, c_3138])).
% 5.66/2.18  tff(c_3851, plain, (![A_187, B_188]: (k2_xboole_0(k2_tarski(A_187, B_188), k2_tarski(A_187, B_188))=k2_xboole_0(k1_tarski(A_187), k2_tarski(A_187, B_188)))), inference(superposition, [status(thm), theory('equality')], [c_3842, c_3263])).
% 5.66/2.18  tff(c_3946, plain, (![A_187, B_188]: (k1_enumset1(A_187, A_187, B_188)=k2_tarski(A_187, B_188))), inference(demodulation, [status(thm), theory('equality')], [c_581, c_26, c_3851])).
% 5.66/2.18  tff(c_30, plain, (k1_enumset1('#skF_3', '#skF_3', '#skF_4')!=k2_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.66/2.18  tff(c_3974, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3946, c_30])).
% 5.66/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.66/2.18  
% 5.66/2.18  Inference rules
% 5.66/2.18  ----------------------
% 5.66/2.18  #Ref     : 0
% 5.66/2.18  #Sup     : 858
% 5.66/2.18  #Fact    : 16
% 5.66/2.18  #Define  : 0
% 5.66/2.18  #Split   : 0
% 5.66/2.18  #Chain   : 0
% 5.66/2.18  #Close   : 0
% 5.66/2.18  
% 5.66/2.18  Ordering : KBO
% 5.66/2.18  
% 5.66/2.18  Simplification rules
% 5.66/2.18  ----------------------
% 5.66/2.18  #Subsume      : 198
% 5.66/2.18  #Demod        : 1124
% 5.66/2.18  #Tautology    : 215
% 5.66/2.18  #SimpNegUnit  : 0
% 5.66/2.18  #BackRed      : 6
% 5.66/2.18  
% 5.66/2.18  #Partial instantiations: 0
% 5.66/2.18  #Strategies tried      : 1
% 5.66/2.18  
% 5.66/2.18  Timing (in seconds)
% 5.66/2.18  ----------------------
% 5.66/2.19  Preprocessing        : 0.32
% 5.66/2.19  Parsing              : 0.16
% 5.66/2.19  CNF conversion       : 0.02
% 5.66/2.19  Main loop            : 1.01
% 5.66/2.19  Inferencing          : 0.36
% 5.66/2.19  Reduction            : 0.32
% 5.66/2.19  Demodulation         : 0.25
% 5.66/2.19  BG Simplification    : 0.05
% 5.66/2.19  Subsumption          : 0.22
% 5.66/2.19  Abstraction          : 0.07
% 5.66/2.19  MUC search           : 0.00
% 5.66/2.19  Cooper               : 0.00
% 5.66/2.19  Total                : 1.36
% 5.66/2.19  Index Insertion      : 0.00
% 5.66/2.19  Index Deletion       : 0.00
% 5.66/2.19  Index Matching       : 0.00
% 5.66/2.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
