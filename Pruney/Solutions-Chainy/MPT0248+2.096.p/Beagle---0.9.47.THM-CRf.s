%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:17 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 210 expanded)
%              Number of leaves         :   36 (  83 expanded)
%              Depth                    :   13
%              Number of atoms          :  129 ( 468 expanded)
%              Number of equality atoms :   61 ( 342 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_5 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_119,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_44,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_93,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(c_82,plain,
    ( k1_tarski('#skF_6') != '#skF_8'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_129,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_22,plain,(
    ! [A_9] :
      ( r2_hidden('#skF_3'(A_9),A_9)
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_86,plain,(
    k2_xboole_0('#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_231,plain,(
    ! [D_90,A_91,B_92] :
      ( ~ r2_hidden(D_90,A_91)
      | r2_hidden(D_90,k2_xboole_0(A_91,B_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_247,plain,(
    ! [D_95] :
      ( ~ r2_hidden(D_95,'#skF_7')
      | r2_hidden(D_95,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_231])).

tff(c_44,plain,(
    ! [C_31,A_27] :
      ( C_31 = A_27
      | ~ r2_hidden(C_31,k1_tarski(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_252,plain,(
    ! [D_96] :
      ( D_96 = '#skF_6'
      | ~ r2_hidden(D_96,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_247,c_44])).

tff(c_256,plain,
    ( '#skF_3'('#skF_7') = '#skF_6'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_22,c_252])).

tff(c_259,plain,(
    '#skF_3'('#skF_7') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_256])).

tff(c_263,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_22])).

tff(c_266,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_263])).

tff(c_72,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(k1_tarski(A_60),B_61)
      | ~ r2_hidden(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_80,plain,
    ( k1_xboole_0 != '#skF_8'
    | k1_tarski('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_130,plain,(
    k1_tarski('#skF_6') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_28,plain,(
    ! [B_12] : r1_tarski(B_12,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_301,plain,(
    ! [A_102,C_103,B_104] :
      ( r1_tarski(A_102,C_103)
      | ~ r1_tarski(k2_xboole_0(A_102,B_104),C_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_339,plain,(
    ! [C_107] :
      ( r1_tarski('#skF_7',C_107)
      | ~ r1_tarski(k1_tarski('#skF_6'),C_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_301])).

tff(c_349,plain,(
    r1_tarski('#skF_7',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_28,c_339])).

tff(c_24,plain,(
    ! [B_12,A_11] :
      ( B_12 = A_11
      | ~ r1_tarski(B_12,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_351,plain,
    ( k1_tarski('#skF_6') = '#skF_7'
    | ~ r1_tarski(k1_tarski('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_349,c_24])).

tff(c_357,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_351])).

tff(c_361,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_357])).

tff(c_365,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_361])).

tff(c_367,plain,(
    k1_tarski('#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_84,plain,
    ( k1_tarski('#skF_6') != '#skF_8'
    | k1_tarski('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_405,plain,(
    '#skF_7' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_367,c_84])).

tff(c_366,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_368,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_86])).

tff(c_672,plain,(
    ! [D_145,B_146,A_147] :
      ( ~ r2_hidden(D_145,B_146)
      | r2_hidden(D_145,k2_xboole_0(A_147,B_146)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_684,plain,(
    ! [D_148] :
      ( ~ r2_hidden(D_148,'#skF_8')
      | r2_hidden(D_148,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_368,c_672])).

tff(c_389,plain,(
    ! [C_109,A_110] :
      ( C_109 = A_110
      | ~ r2_hidden(C_109,k1_tarski(A_110)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_392,plain,(
    ! [C_109] :
      ( C_109 = '#skF_6'
      | ~ r2_hidden(C_109,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_389])).

tff(c_711,plain,(
    ! [D_151] :
      ( D_151 = '#skF_6'
      | ~ r2_hidden(D_151,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_684,c_392])).

tff(c_719,plain,
    ( '#skF_3'('#skF_8') = '#skF_6'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_22,c_711])).

tff(c_724,plain,(
    '#skF_3'('#skF_8') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_366,c_719])).

tff(c_728,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_724,c_22])).

tff(c_731,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_366,c_728])).

tff(c_428,plain,(
    ! [A_113,B_114] :
      ( r1_tarski(k1_tarski(A_113),B_114)
      | ~ r2_hidden(A_113,B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_431,plain,(
    ! [B_114] :
      ( r1_tarski('#skF_7',B_114)
      | ~ r2_hidden('#skF_6',B_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_428])).

tff(c_741,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_731,c_431])).

tff(c_34,plain,(
    ! [A_18,B_19] :
      ( k2_xboole_0(A_18,B_19) = B_19
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_750,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_741,c_34])).

tff(c_751,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_750,c_368])).

tff(c_753,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_405,c_751])).

tff(c_754,plain,(
    k1_tarski('#skF_6') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_20,plain,(
    ! [A_7] : k2_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_755,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_805,plain,(
    ! [A_9] :
      ( r2_hidden('#skF_3'(A_9),A_9)
      | A_9 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_755,c_22])).

tff(c_1064,plain,(
    ! [D_191,B_192,A_193] :
      ( ~ r2_hidden(D_191,B_192)
      | r2_hidden(D_191,k2_xboole_0(A_193,B_192)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1097,plain,(
    ! [D_196] :
      ( ~ r2_hidden(D_196,'#skF_8')
      | r2_hidden(D_196,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_1064])).

tff(c_1108,plain,(
    ! [D_197] :
      ( D_197 = '#skF_6'
      | ~ r2_hidden(D_197,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1097,c_44])).

tff(c_1113,plain,
    ( '#skF_3'('#skF_8') = '#skF_6'
    | '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_805,c_1108])).

tff(c_1114,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1113])).

tff(c_1130,plain,(
    k2_xboole_0('#skF_8','#skF_8') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1114,c_86])).

tff(c_1131,plain,(
    k1_tarski('#skF_6') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1130])).

tff(c_1133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_754,c_1131])).

tff(c_1135,plain,(
    '#skF_7' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1113])).

tff(c_1134,plain,(
    '#skF_3'('#skF_8') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1113])).

tff(c_1139,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | '#skF_7' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_1134,c_805])).

tff(c_1142,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_1135,c_1139])).

tff(c_889,plain,(
    ! [A_173,C_174,B_175] :
      ( r1_tarski(A_173,C_174)
      | ~ r1_tarski(k2_xboole_0(A_173,B_175),C_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_966,plain,(
    ! [C_182] :
      ( r1_tarski('#skF_7',C_182)
      | ~ r1_tarski(k1_tarski('#skF_6'),C_182) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_889])).

tff(c_980,plain,(
    ! [B_61] :
      ( r1_tarski('#skF_7',B_61)
      | ~ r2_hidden('#skF_6',B_61) ) ),
    inference(resolution,[status(thm)],[c_72,c_966])).

tff(c_1152,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_1142,c_980])).

tff(c_1170,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1152,c_34])).

tff(c_1171,plain,(
    k1_tarski('#skF_6') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1170,c_86])).

tff(c_1173,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_754,c_1171])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:15:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.51  
% 3.35/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.52  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 3.35/1.52  
% 3.35/1.52  %Foreground sorts:
% 3.35/1.52  
% 3.35/1.52  
% 3.35/1.52  %Background operators:
% 3.35/1.52  
% 3.35/1.52  
% 3.35/1.52  %Foreground operators:
% 3.35/1.52  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.35/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.35/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.35/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.35/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.35/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.35/1.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.35/1.52  tff('#skF_7', type, '#skF_7': $i).
% 3.35/1.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.35/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.35/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.35/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.35/1.52  tff('#skF_6', type, '#skF_6': $i).
% 3.35/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.35/1.52  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.35/1.52  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.35/1.52  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.35/1.52  tff('#skF_8', type, '#skF_8': $i).
% 3.35/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.35/1.52  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.35/1.52  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.35/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.35/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.35/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.35/1.52  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.35/1.52  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.35/1.52  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.35/1.52  
% 3.35/1.53  tff(f_119, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.35/1.53  tff(f_44, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.35/1.53  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.35/1.53  tff(f_75, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.35/1.53  tff(f_93, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.35/1.53  tff(f_50, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.35/1.53  tff(f_56, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 3.35/1.53  tff(f_60, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.35/1.53  tff(f_36, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.35/1.53  tff(c_82, plain, (k1_tarski('#skF_6')!='#skF_8' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.35/1.53  tff(c_129, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_82])).
% 3.35/1.53  tff(c_22, plain, (![A_9]: (r2_hidden('#skF_3'(A_9), A_9) | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.35/1.53  tff(c_86, plain, (k2_xboole_0('#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.35/1.53  tff(c_231, plain, (![D_90, A_91, B_92]: (~r2_hidden(D_90, A_91) | r2_hidden(D_90, k2_xboole_0(A_91, B_92)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.35/1.53  tff(c_247, plain, (![D_95]: (~r2_hidden(D_95, '#skF_7') | r2_hidden(D_95, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_86, c_231])).
% 3.35/1.53  tff(c_44, plain, (![C_31, A_27]: (C_31=A_27 | ~r2_hidden(C_31, k1_tarski(A_27)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.35/1.53  tff(c_252, plain, (![D_96]: (D_96='#skF_6' | ~r2_hidden(D_96, '#skF_7'))), inference(resolution, [status(thm)], [c_247, c_44])).
% 3.35/1.53  tff(c_256, plain, ('#skF_3'('#skF_7')='#skF_6' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_22, c_252])).
% 3.35/1.53  tff(c_259, plain, ('#skF_3'('#skF_7')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_129, c_256])).
% 3.35/1.53  tff(c_263, plain, (r2_hidden('#skF_6', '#skF_7') | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_259, c_22])).
% 3.35/1.53  tff(c_266, plain, (r2_hidden('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_129, c_263])).
% 3.35/1.53  tff(c_72, plain, (![A_60, B_61]: (r1_tarski(k1_tarski(A_60), B_61) | ~r2_hidden(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.35/1.53  tff(c_80, plain, (k1_xboole_0!='#skF_8' | k1_tarski('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.35/1.53  tff(c_130, plain, (k1_tarski('#skF_6')!='#skF_7'), inference(splitLeft, [status(thm)], [c_80])).
% 3.35/1.53  tff(c_28, plain, (![B_12]: (r1_tarski(B_12, B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.35/1.53  tff(c_301, plain, (![A_102, C_103, B_104]: (r1_tarski(A_102, C_103) | ~r1_tarski(k2_xboole_0(A_102, B_104), C_103))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.35/1.53  tff(c_339, plain, (![C_107]: (r1_tarski('#skF_7', C_107) | ~r1_tarski(k1_tarski('#skF_6'), C_107))), inference(superposition, [status(thm), theory('equality')], [c_86, c_301])).
% 3.35/1.53  tff(c_349, plain, (r1_tarski('#skF_7', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_28, c_339])).
% 3.35/1.53  tff(c_24, plain, (![B_12, A_11]: (B_12=A_11 | ~r1_tarski(B_12, A_11) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.35/1.53  tff(c_351, plain, (k1_tarski('#skF_6')='#skF_7' | ~r1_tarski(k1_tarski('#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_349, c_24])).
% 3.35/1.53  tff(c_357, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_130, c_351])).
% 3.35/1.53  tff(c_361, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_72, c_357])).
% 3.35/1.53  tff(c_365, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_266, c_361])).
% 3.35/1.53  tff(c_367, plain, (k1_tarski('#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_80])).
% 3.35/1.53  tff(c_84, plain, (k1_tarski('#skF_6')!='#skF_8' | k1_tarski('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.35/1.53  tff(c_405, plain, ('#skF_7'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_367, c_367, c_84])).
% 3.35/1.53  tff(c_366, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_80])).
% 3.35/1.53  tff(c_368, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_367, c_86])).
% 3.35/1.53  tff(c_672, plain, (![D_145, B_146, A_147]: (~r2_hidden(D_145, B_146) | r2_hidden(D_145, k2_xboole_0(A_147, B_146)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.35/1.53  tff(c_684, plain, (![D_148]: (~r2_hidden(D_148, '#skF_8') | r2_hidden(D_148, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_368, c_672])).
% 3.35/1.53  tff(c_389, plain, (![C_109, A_110]: (C_109=A_110 | ~r2_hidden(C_109, k1_tarski(A_110)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.35/1.53  tff(c_392, plain, (![C_109]: (C_109='#skF_6' | ~r2_hidden(C_109, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_367, c_389])).
% 3.35/1.53  tff(c_711, plain, (![D_151]: (D_151='#skF_6' | ~r2_hidden(D_151, '#skF_8'))), inference(resolution, [status(thm)], [c_684, c_392])).
% 3.35/1.53  tff(c_719, plain, ('#skF_3'('#skF_8')='#skF_6' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_22, c_711])).
% 3.35/1.53  tff(c_724, plain, ('#skF_3'('#skF_8')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_366, c_719])).
% 3.35/1.53  tff(c_728, plain, (r2_hidden('#skF_6', '#skF_8') | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_724, c_22])).
% 3.35/1.53  tff(c_731, plain, (r2_hidden('#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_366, c_728])).
% 3.35/1.53  tff(c_428, plain, (![A_113, B_114]: (r1_tarski(k1_tarski(A_113), B_114) | ~r2_hidden(A_113, B_114))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.35/1.53  tff(c_431, plain, (![B_114]: (r1_tarski('#skF_7', B_114) | ~r2_hidden('#skF_6', B_114))), inference(superposition, [status(thm), theory('equality')], [c_367, c_428])).
% 3.35/1.53  tff(c_741, plain, (r1_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_731, c_431])).
% 3.35/1.53  tff(c_34, plain, (![A_18, B_19]: (k2_xboole_0(A_18, B_19)=B_19 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.35/1.53  tff(c_750, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_741, c_34])).
% 3.35/1.53  tff(c_751, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_750, c_368])).
% 3.35/1.53  tff(c_753, plain, $false, inference(negUnitSimplification, [status(thm)], [c_405, c_751])).
% 3.35/1.53  tff(c_754, plain, (k1_tarski('#skF_6')!='#skF_8'), inference(splitRight, [status(thm)], [c_82])).
% 3.35/1.53  tff(c_20, plain, (![A_7]: (k2_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.35/1.53  tff(c_755, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_82])).
% 3.35/1.53  tff(c_805, plain, (![A_9]: (r2_hidden('#skF_3'(A_9), A_9) | A_9='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_755, c_22])).
% 3.35/1.53  tff(c_1064, plain, (![D_191, B_192, A_193]: (~r2_hidden(D_191, B_192) | r2_hidden(D_191, k2_xboole_0(A_193, B_192)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.35/1.53  tff(c_1097, plain, (![D_196]: (~r2_hidden(D_196, '#skF_8') | r2_hidden(D_196, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_86, c_1064])).
% 3.35/1.53  tff(c_1108, plain, (![D_197]: (D_197='#skF_6' | ~r2_hidden(D_197, '#skF_8'))), inference(resolution, [status(thm)], [c_1097, c_44])).
% 3.35/1.53  tff(c_1113, plain, ('#skF_3'('#skF_8')='#skF_6' | '#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_805, c_1108])).
% 3.35/1.53  tff(c_1114, plain, ('#skF_7'='#skF_8'), inference(splitLeft, [status(thm)], [c_1113])).
% 3.35/1.53  tff(c_1130, plain, (k2_xboole_0('#skF_8', '#skF_8')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1114, c_86])).
% 3.35/1.53  tff(c_1131, plain, (k1_tarski('#skF_6')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1130])).
% 3.35/1.53  tff(c_1133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_754, c_1131])).
% 3.35/1.53  tff(c_1135, plain, ('#skF_7'!='#skF_8'), inference(splitRight, [status(thm)], [c_1113])).
% 3.35/1.53  tff(c_1134, plain, ('#skF_3'('#skF_8')='#skF_6'), inference(splitRight, [status(thm)], [c_1113])).
% 3.35/1.53  tff(c_1139, plain, (r2_hidden('#skF_6', '#skF_8') | '#skF_7'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_1134, c_805])).
% 3.35/1.53  tff(c_1142, plain, (r2_hidden('#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_1135, c_1139])).
% 3.35/1.53  tff(c_889, plain, (![A_173, C_174, B_175]: (r1_tarski(A_173, C_174) | ~r1_tarski(k2_xboole_0(A_173, B_175), C_174))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.35/1.53  tff(c_966, plain, (![C_182]: (r1_tarski('#skF_7', C_182) | ~r1_tarski(k1_tarski('#skF_6'), C_182))), inference(superposition, [status(thm), theory('equality')], [c_86, c_889])).
% 3.35/1.53  tff(c_980, plain, (![B_61]: (r1_tarski('#skF_7', B_61) | ~r2_hidden('#skF_6', B_61))), inference(resolution, [status(thm)], [c_72, c_966])).
% 3.35/1.53  tff(c_1152, plain, (r1_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_1142, c_980])).
% 3.35/1.53  tff(c_1170, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_1152, c_34])).
% 3.35/1.53  tff(c_1171, plain, (k1_tarski('#skF_6')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1170, c_86])).
% 3.35/1.53  tff(c_1173, plain, $false, inference(negUnitSimplification, [status(thm)], [c_754, c_1171])).
% 3.35/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.53  
% 3.35/1.53  Inference rules
% 3.35/1.53  ----------------------
% 3.35/1.53  #Ref     : 0
% 3.35/1.53  #Sup     : 233
% 3.35/1.53  #Fact    : 0
% 3.35/1.53  #Define  : 0
% 3.35/1.53  #Split   : 6
% 3.35/1.53  #Chain   : 0
% 3.35/1.53  #Close   : 0
% 3.35/1.53  
% 3.35/1.53  Ordering : KBO
% 3.35/1.53  
% 3.35/1.53  Simplification rules
% 3.35/1.53  ----------------------
% 3.35/1.53  #Subsume      : 8
% 3.35/1.53  #Demod        : 85
% 3.35/1.53  #Tautology    : 147
% 3.35/1.53  #SimpNegUnit  : 15
% 3.35/1.53  #BackRed      : 26
% 3.35/1.53  
% 3.35/1.53  #Partial instantiations: 0
% 3.35/1.53  #Strategies tried      : 1
% 3.35/1.53  
% 3.35/1.53  Timing (in seconds)
% 3.35/1.53  ----------------------
% 3.35/1.54  Preprocessing        : 0.37
% 3.35/1.54  Parsing              : 0.19
% 3.35/1.54  CNF conversion       : 0.03
% 3.35/1.54  Main loop            : 0.39
% 3.35/1.54  Inferencing          : 0.14
% 3.35/1.54  Reduction            : 0.12
% 3.35/1.54  Demodulation         : 0.08
% 3.35/1.54  BG Simplification    : 0.03
% 3.35/1.54  Subsumption          : 0.07
% 3.35/1.54  Abstraction          : 0.02
% 3.35/1.54  MUC search           : 0.00
% 3.35/1.54  Cooper               : 0.00
% 3.35/1.54  Total                : 0.80
% 3.35/1.54  Index Insertion      : 0.00
% 3.35/1.54  Index Deletion       : 0.00
% 3.35/1.54  Index Matching       : 0.00
% 3.35/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
