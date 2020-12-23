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
% DateTime   : Thu Dec  3 09:57:18 EST 2020

% Result     : Theorem 17.10s
% Output     : CNFRefutation 17.10s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 208 expanded)
%              Number of leaves         :   31 (  83 expanded)
%              Depth                    :   15
%              Number of atoms          :  124 ( 409 expanded)
%              Number of equality atoms :   39 ( 119 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_8 > #skF_9 > #skF_4 > #skF_5 > #skF_3 > #skF_7 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(k1_setfam_1(B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_50,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_76,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(B,C) )
     => ( A = k1_xboole_0
        | r1_tarski(B,k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_82,plain,(
    k1_setfam_1(k1_tarski('#skF_9')) != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_38,plain,(
    ! [E_21,A_15,C_17] : r2_hidden(E_21,k1_enumset1(A_15,E_21,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_30,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_257,plain,(
    ! [B_83,C_84,A_85] :
      ( r1_tarski(k1_setfam_1(B_83),C_84)
      | ~ r1_tarski(A_85,C_84)
      | ~ r2_hidden(A_85,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_284,plain,(
    ! [B_89,B_90] :
      ( r1_tarski(k1_setfam_1(B_89),B_90)
      | ~ r2_hidden(B_90,B_89) ) ),
    inference(resolution,[status(thm)],[c_30,c_257])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_32,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_157,plain,(
    ! [D_65,B_66,A_67] :
      ( ~ r2_hidden(D_65,B_66)
      | ~ r2_hidden(D_65,k4_xboole_0(A_67,B_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_166,plain,(
    ! [D_68,A_69] :
      ( ~ r2_hidden(D_68,k1_xboole_0)
      | ~ r2_hidden(D_68,A_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_157])).

tff(c_194,plain,(
    ! [B_77,A_78] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0,B_77),A_78)
      | r1_tarski(k1_xboole_0,B_77) ) ),
    inference(resolution,[status(thm)],[c_6,c_166])).

tff(c_225,plain,(
    ! [B_79] : r1_tarski(k1_xboole_0,B_79) ),
    inference(resolution,[status(thm)],[c_6,c_194])).

tff(c_26,plain,(
    ! [B_13,A_12] :
      ( B_13 = A_12
      | ~ r1_tarski(B_13,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_228,plain,(
    ! [B_79] :
      ( k1_xboole_0 = B_79
      | ~ r1_tarski(B_79,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_225,c_26])).

tff(c_296,plain,(
    ! [B_91] :
      ( k1_setfam_1(B_91) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,B_91) ) ),
    inference(resolution,[status(thm)],[c_284,c_228])).

tff(c_323,plain,(
    ! [A_15,C_17] : k1_setfam_1(k1_enumset1(A_15,k1_xboole_0,C_17)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_296])).

tff(c_113,plain,(
    ! [A_54,B_55] : k1_enumset1(A_54,A_54,B_55) = k2_tarski(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_36,plain,(
    ! [E_21,A_15,B_16] : r2_hidden(E_21,k1_enumset1(A_15,B_16,E_21)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_122,plain,(
    ! [B_55,A_54] : r2_hidden(B_55,k2_tarski(A_54,B_55)) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_36])).

tff(c_217,plain,(
    ! [B_2] : r1_tarski(k1_xboole_0,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_194])).

tff(c_262,plain,(
    ! [B_83,B_2] :
      ( r1_tarski(k1_setfam_1(B_83),B_2)
      | ~ r2_hidden(k1_xboole_0,B_83) ) ),
    inference(resolution,[status(thm)],[c_217,c_257])).

tff(c_146,plain,(
    ! [A_63,B_64] :
      ( r2_hidden('#skF_1'(A_63,B_64),A_63)
      | r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_23395,plain,(
    ! [A_23503,B_23504,B_23505] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_23503,B_23504),B_23505),A_23503)
      | r1_tarski(k4_xboole_0(A_23503,B_23504),B_23505) ) ),
    inference(resolution,[status(thm)],[c_146,c_12])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_23482,plain,(
    ! [A_23646,B_23647] : r1_tarski(k4_xboole_0(A_23646,B_23647),A_23646) ),
    inference(resolution,[status(thm)],[c_23395,c_4])).

tff(c_24528,plain,(
    ! [A_25069,B_25070] :
      ( k4_xboole_0(A_25069,B_25070) = A_25069
      | ~ r1_tarski(A_25069,k4_xboole_0(A_25069,B_25070)) ) ),
    inference(resolution,[status(thm)],[c_23482,c_26])).

tff(c_26286,plain,(
    ! [B_26215,B_26216] :
      ( k4_xboole_0(k1_setfam_1(B_26215),B_26216) = k1_setfam_1(B_26215)
      | ~ r2_hidden(k1_xboole_0,B_26215) ) ),
    inference(resolution,[status(thm)],[c_262,c_24528])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_28615,plain,(
    ! [D_28204,B_28205,B_28206] :
      ( ~ r2_hidden(D_28204,B_28205)
      | ~ r2_hidden(D_28204,k1_setfam_1(B_28206))
      | ~ r2_hidden(k1_xboole_0,B_28206) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26286,c_10])).

tff(c_28682,plain,(
    ! [B_28347,B_28348] :
      ( ~ r2_hidden(B_28347,k1_setfam_1(B_28348))
      | ~ r2_hidden(k1_xboole_0,B_28348) ) ),
    inference(resolution,[status(thm)],[c_122,c_28615])).

tff(c_28782,plain,(
    ! [B_28347,A_15,C_17] :
      ( ~ r2_hidden(B_28347,k1_xboole_0)
      | ~ r2_hidden(k1_xboole_0,k1_enumset1(A_15,k1_xboole_0,C_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_28682])).

tff(c_28817,plain,(
    ! [B_28347] : ~ r2_hidden(B_28347,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_28782])).

tff(c_1149,plain,(
    ! [A_1865,B_1866] :
      ( r2_hidden('#skF_8'(A_1865,B_1866),A_1865)
      | r1_tarski(B_1866,k1_setfam_1(A_1865))
      | k1_xboole_0 = A_1865 ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_58,plain,(
    ! [C_26,A_22] :
      ( C_26 = A_22
      | ~ r2_hidden(C_26,k1_tarski(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1173,plain,(
    ! [A_22,B_1866] :
      ( '#skF_8'(k1_tarski(A_22),B_1866) = A_22
      | r1_tarski(B_1866,k1_setfam_1(k1_tarski(A_22)))
      | k1_tarski(A_22) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1149,c_58])).

tff(c_60,plain,(
    ! [C_26] : r2_hidden(C_26,k1_tarski(C_26)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_80,plain,(
    ! [B_37,C_38,A_36] :
      ( r1_tarski(k1_setfam_1(B_37),C_38)
      | ~ r1_tarski(A_36,C_38)
      | ~ r2_hidden(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_23544,plain,(
    ! [B_23788,A_23789,B_23790] :
      ( r1_tarski(k1_setfam_1(B_23788),A_23789)
      | ~ r2_hidden(k4_xboole_0(A_23789,B_23790),B_23788) ) ),
    inference(resolution,[status(thm)],[c_23482,c_80])).

tff(c_23598,plain,(
    ! [A_23931,B_23932] : r1_tarski(k1_setfam_1(k1_tarski(k4_xboole_0(A_23931,B_23932))),A_23931) ),
    inference(resolution,[status(thm)],[c_60,c_23544])).

tff(c_23981,plain,(
    ! [A_24216] : r1_tarski(k1_setfam_1(k1_tarski(A_24216)),A_24216) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_23598])).

tff(c_26513,plain,(
    ! [A_26500] :
      ( k1_setfam_1(k1_tarski(A_26500)) = A_26500
      | ~ r1_tarski(A_26500,k1_setfam_1(k1_tarski(A_26500))) ) ),
    inference(resolution,[status(thm)],[c_23981,c_26])).

tff(c_74613,plain,(
    ! [A_74481] :
      ( k1_setfam_1(k1_tarski(A_74481)) = A_74481
      | '#skF_8'(k1_tarski(A_74481),A_74481) = A_74481
      | k1_tarski(A_74481) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1173,c_26513])).

tff(c_75152,plain,
    ( '#skF_8'(k1_tarski('#skF_9'),'#skF_9') = '#skF_9'
    | k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_74613,c_82])).

tff(c_75163,plain,(
    k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_75152])).

tff(c_75287,plain,(
    r2_hidden('#skF_9',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_75163,c_60])).

tff(c_75346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28817,c_75287])).

tff(c_75348,plain,(
    k1_tarski('#skF_9') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_75152])).

tff(c_75347,plain,(
    '#skF_8'(k1_tarski('#skF_9'),'#skF_9') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_75152])).

tff(c_76,plain,(
    ! [B_34,A_33] :
      ( ~ r1_tarski(B_34,'#skF_8'(A_33,B_34))
      | r1_tarski(B_34,k1_setfam_1(A_33))
      | k1_xboole_0 = A_33 ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_80590,plain,
    ( ~ r1_tarski('#skF_9','#skF_9')
    | r1_tarski('#skF_9',k1_setfam_1(k1_tarski('#skF_9')))
    | k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_75347,c_76])).

tff(c_80640,plain,
    ( r1_tarski('#skF_9',k1_setfam_1(k1_tarski('#skF_9')))
    | k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_80590])).

tff(c_80641,plain,(
    r1_tarski('#skF_9',k1_setfam_1(k1_tarski('#skF_9'))) ),
    inference(negUnitSimplification,[status(thm)],[c_75348,c_80640])).

tff(c_24076,plain,(
    ! [A_24216] :
      ( k1_setfam_1(k1_tarski(A_24216)) = A_24216
      | ~ r1_tarski(A_24216,k1_setfam_1(k1_tarski(A_24216))) ) ),
    inference(resolution,[status(thm)],[c_23981,c_26])).

tff(c_80652,plain,(
    k1_setfam_1(k1_tarski('#skF_9')) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_80641,c_24076])).

tff(c_80715,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_80652])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:36:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.10/8.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.10/8.40  
% 17.10/8.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.10/8.40  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_8 > #skF_9 > #skF_4 > #skF_5 > #skF_3 > #skF_7 > #skF_1
% 17.10/8.40  
% 17.10/8.40  %Foreground sorts:
% 17.10/8.40  
% 17.10/8.40  
% 17.10/8.40  %Background operators:
% 17.10/8.40  
% 17.10/8.40  
% 17.10/8.40  %Foreground operators:
% 17.10/8.40  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 17.10/8.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.10/8.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.10/8.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 17.10/8.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 17.10/8.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.10/8.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.10/8.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 17.10/8.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 17.10/8.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 17.10/8.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 17.10/8.40  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 17.10/8.40  tff('#skF_9', type, '#skF_9': $i).
% 17.10/8.40  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 17.10/8.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.10/8.40  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 17.10/8.40  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 17.10/8.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.10/8.40  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 17.10/8.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 17.10/8.40  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 17.10/8.40  
% 17.10/8.41  tff(f_96, negated_conjecture, ~(![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 17.10/8.41  tff(f_65, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 17.10/8.41  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 17.10/8.41  tff(f_93, axiom, (![A, B, C]: ((r2_hidden(A, B) & r1_tarski(A, C)) => r1_tarski(k1_setfam_1(B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_setfam_1)).
% 17.10/8.41  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 17.10/8.41  tff(f_50, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 17.10/8.41  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 17.10/8.41  tff(f_76, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 17.10/8.41  tff(f_87, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(B, C))) => ((A = k1_xboole_0) | r1_tarski(B, k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_setfam_1)).
% 17.10/8.41  tff(f_72, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 17.10/8.41  tff(c_82, plain, (k1_setfam_1(k1_tarski('#skF_9'))!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_96])).
% 17.10/8.41  tff(c_38, plain, (![E_21, A_15, C_17]: (r2_hidden(E_21, k1_enumset1(A_15, E_21, C_17)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 17.10/8.41  tff(c_30, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 17.10/8.41  tff(c_257, plain, (![B_83, C_84, A_85]: (r1_tarski(k1_setfam_1(B_83), C_84) | ~r1_tarski(A_85, C_84) | ~r2_hidden(A_85, B_83))), inference(cnfTransformation, [status(thm)], [f_93])).
% 17.10/8.41  tff(c_284, plain, (![B_89, B_90]: (r1_tarski(k1_setfam_1(B_89), B_90) | ~r2_hidden(B_90, B_89))), inference(resolution, [status(thm)], [c_30, c_257])).
% 17.10/8.41  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.10/8.41  tff(c_32, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_50])).
% 17.10/8.41  tff(c_157, plain, (![D_65, B_66, A_67]: (~r2_hidden(D_65, B_66) | ~r2_hidden(D_65, k4_xboole_0(A_67, B_66)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 17.10/8.41  tff(c_166, plain, (![D_68, A_69]: (~r2_hidden(D_68, k1_xboole_0) | ~r2_hidden(D_68, A_69))), inference(superposition, [status(thm), theory('equality')], [c_32, c_157])).
% 17.10/8.41  tff(c_194, plain, (![B_77, A_78]: (~r2_hidden('#skF_1'(k1_xboole_0, B_77), A_78) | r1_tarski(k1_xboole_0, B_77))), inference(resolution, [status(thm)], [c_6, c_166])).
% 17.10/8.41  tff(c_225, plain, (![B_79]: (r1_tarski(k1_xboole_0, B_79))), inference(resolution, [status(thm)], [c_6, c_194])).
% 17.10/8.41  tff(c_26, plain, (![B_13, A_12]: (B_13=A_12 | ~r1_tarski(B_13, A_12) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 17.10/8.41  tff(c_228, plain, (![B_79]: (k1_xboole_0=B_79 | ~r1_tarski(B_79, k1_xboole_0))), inference(resolution, [status(thm)], [c_225, c_26])).
% 17.10/8.41  tff(c_296, plain, (![B_91]: (k1_setfam_1(B_91)=k1_xboole_0 | ~r2_hidden(k1_xboole_0, B_91))), inference(resolution, [status(thm)], [c_284, c_228])).
% 17.10/8.41  tff(c_323, plain, (![A_15, C_17]: (k1_setfam_1(k1_enumset1(A_15, k1_xboole_0, C_17))=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_296])).
% 17.10/8.41  tff(c_113, plain, (![A_54, B_55]: (k1_enumset1(A_54, A_54, B_55)=k2_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_76])).
% 17.10/8.41  tff(c_36, plain, (![E_21, A_15, B_16]: (r2_hidden(E_21, k1_enumset1(A_15, B_16, E_21)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 17.10/8.41  tff(c_122, plain, (![B_55, A_54]: (r2_hidden(B_55, k2_tarski(A_54, B_55)))), inference(superposition, [status(thm), theory('equality')], [c_113, c_36])).
% 17.10/8.41  tff(c_217, plain, (![B_2]: (r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_194])).
% 17.10/8.41  tff(c_262, plain, (![B_83, B_2]: (r1_tarski(k1_setfam_1(B_83), B_2) | ~r2_hidden(k1_xboole_0, B_83))), inference(resolution, [status(thm)], [c_217, c_257])).
% 17.10/8.41  tff(c_146, plain, (![A_63, B_64]: (r2_hidden('#skF_1'(A_63, B_64), A_63) | r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.10/8.41  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 17.10/8.41  tff(c_23395, plain, (![A_23503, B_23504, B_23505]: (r2_hidden('#skF_1'(k4_xboole_0(A_23503, B_23504), B_23505), A_23503) | r1_tarski(k4_xboole_0(A_23503, B_23504), B_23505))), inference(resolution, [status(thm)], [c_146, c_12])).
% 17.10/8.41  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.10/8.41  tff(c_23482, plain, (![A_23646, B_23647]: (r1_tarski(k4_xboole_0(A_23646, B_23647), A_23646))), inference(resolution, [status(thm)], [c_23395, c_4])).
% 17.10/8.41  tff(c_24528, plain, (![A_25069, B_25070]: (k4_xboole_0(A_25069, B_25070)=A_25069 | ~r1_tarski(A_25069, k4_xboole_0(A_25069, B_25070)))), inference(resolution, [status(thm)], [c_23482, c_26])).
% 17.10/8.41  tff(c_26286, plain, (![B_26215, B_26216]: (k4_xboole_0(k1_setfam_1(B_26215), B_26216)=k1_setfam_1(B_26215) | ~r2_hidden(k1_xboole_0, B_26215))), inference(resolution, [status(thm)], [c_262, c_24528])).
% 17.10/8.41  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 17.10/8.41  tff(c_28615, plain, (![D_28204, B_28205, B_28206]: (~r2_hidden(D_28204, B_28205) | ~r2_hidden(D_28204, k1_setfam_1(B_28206)) | ~r2_hidden(k1_xboole_0, B_28206))), inference(superposition, [status(thm), theory('equality')], [c_26286, c_10])).
% 17.10/8.41  tff(c_28682, plain, (![B_28347, B_28348]: (~r2_hidden(B_28347, k1_setfam_1(B_28348)) | ~r2_hidden(k1_xboole_0, B_28348))), inference(resolution, [status(thm)], [c_122, c_28615])).
% 17.10/8.41  tff(c_28782, plain, (![B_28347, A_15, C_17]: (~r2_hidden(B_28347, k1_xboole_0) | ~r2_hidden(k1_xboole_0, k1_enumset1(A_15, k1_xboole_0, C_17)))), inference(superposition, [status(thm), theory('equality')], [c_323, c_28682])).
% 17.10/8.41  tff(c_28817, plain, (![B_28347]: (~r2_hidden(B_28347, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_28782])).
% 17.10/8.41  tff(c_1149, plain, (![A_1865, B_1866]: (r2_hidden('#skF_8'(A_1865, B_1866), A_1865) | r1_tarski(B_1866, k1_setfam_1(A_1865)) | k1_xboole_0=A_1865)), inference(cnfTransformation, [status(thm)], [f_87])).
% 17.10/8.41  tff(c_58, plain, (![C_26, A_22]: (C_26=A_22 | ~r2_hidden(C_26, k1_tarski(A_22)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 17.10/8.41  tff(c_1173, plain, (![A_22, B_1866]: ('#skF_8'(k1_tarski(A_22), B_1866)=A_22 | r1_tarski(B_1866, k1_setfam_1(k1_tarski(A_22))) | k1_tarski(A_22)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1149, c_58])).
% 17.10/8.41  tff(c_60, plain, (![C_26]: (r2_hidden(C_26, k1_tarski(C_26)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 17.10/8.41  tff(c_80, plain, (![B_37, C_38, A_36]: (r1_tarski(k1_setfam_1(B_37), C_38) | ~r1_tarski(A_36, C_38) | ~r2_hidden(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_93])).
% 17.10/8.41  tff(c_23544, plain, (![B_23788, A_23789, B_23790]: (r1_tarski(k1_setfam_1(B_23788), A_23789) | ~r2_hidden(k4_xboole_0(A_23789, B_23790), B_23788))), inference(resolution, [status(thm)], [c_23482, c_80])).
% 17.10/8.41  tff(c_23598, plain, (![A_23931, B_23932]: (r1_tarski(k1_setfam_1(k1_tarski(k4_xboole_0(A_23931, B_23932))), A_23931))), inference(resolution, [status(thm)], [c_60, c_23544])).
% 17.10/8.41  tff(c_23981, plain, (![A_24216]: (r1_tarski(k1_setfam_1(k1_tarski(A_24216)), A_24216))), inference(superposition, [status(thm), theory('equality')], [c_32, c_23598])).
% 17.10/8.41  tff(c_26513, plain, (![A_26500]: (k1_setfam_1(k1_tarski(A_26500))=A_26500 | ~r1_tarski(A_26500, k1_setfam_1(k1_tarski(A_26500))))), inference(resolution, [status(thm)], [c_23981, c_26])).
% 17.10/8.41  tff(c_74613, plain, (![A_74481]: (k1_setfam_1(k1_tarski(A_74481))=A_74481 | '#skF_8'(k1_tarski(A_74481), A_74481)=A_74481 | k1_tarski(A_74481)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1173, c_26513])).
% 17.10/8.41  tff(c_75152, plain, ('#skF_8'(k1_tarski('#skF_9'), '#skF_9')='#skF_9' | k1_tarski('#skF_9')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_74613, c_82])).
% 17.10/8.41  tff(c_75163, plain, (k1_tarski('#skF_9')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_75152])).
% 17.10/8.41  tff(c_75287, plain, (r2_hidden('#skF_9', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_75163, c_60])).
% 17.10/8.41  tff(c_75346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28817, c_75287])).
% 17.10/8.41  tff(c_75348, plain, (k1_tarski('#skF_9')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_75152])).
% 17.10/8.41  tff(c_75347, plain, ('#skF_8'(k1_tarski('#skF_9'), '#skF_9')='#skF_9'), inference(splitRight, [status(thm)], [c_75152])).
% 17.10/8.41  tff(c_76, plain, (![B_34, A_33]: (~r1_tarski(B_34, '#skF_8'(A_33, B_34)) | r1_tarski(B_34, k1_setfam_1(A_33)) | k1_xboole_0=A_33)), inference(cnfTransformation, [status(thm)], [f_87])).
% 17.10/8.41  tff(c_80590, plain, (~r1_tarski('#skF_9', '#skF_9') | r1_tarski('#skF_9', k1_setfam_1(k1_tarski('#skF_9'))) | k1_tarski('#skF_9')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_75347, c_76])).
% 17.10/8.41  tff(c_80640, plain, (r1_tarski('#skF_9', k1_setfam_1(k1_tarski('#skF_9'))) | k1_tarski('#skF_9')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_80590])).
% 17.10/8.41  tff(c_80641, plain, (r1_tarski('#skF_9', k1_setfam_1(k1_tarski('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_75348, c_80640])).
% 17.10/8.41  tff(c_24076, plain, (![A_24216]: (k1_setfam_1(k1_tarski(A_24216))=A_24216 | ~r1_tarski(A_24216, k1_setfam_1(k1_tarski(A_24216))))), inference(resolution, [status(thm)], [c_23981, c_26])).
% 17.10/8.41  tff(c_80652, plain, (k1_setfam_1(k1_tarski('#skF_9'))='#skF_9'), inference(resolution, [status(thm)], [c_80641, c_24076])).
% 17.10/8.41  tff(c_80715, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_80652])).
% 17.10/8.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.10/8.41  
% 17.10/8.41  Inference rules
% 17.10/8.41  ----------------------
% 17.10/8.41  #Ref     : 0
% 17.10/8.41  #Sup     : 11750
% 17.10/8.41  #Fact    : 28
% 17.10/8.41  #Define  : 0
% 17.10/8.41  #Split   : 12
% 17.10/8.41  #Chain   : 0
% 17.10/8.41  #Close   : 0
% 17.10/8.41  
% 17.10/8.41  Ordering : KBO
% 17.10/8.41  
% 17.10/8.41  Simplification rules
% 17.10/8.41  ----------------------
% 17.10/8.41  #Subsume      : 3135
% 17.10/8.41  #Demod        : 7482
% 17.10/8.41  #Tautology    : 3532
% 17.10/8.41  #SimpNegUnit  : 79
% 17.10/8.41  #BackRed      : 6
% 17.10/8.42  
% 17.10/8.42  #Partial instantiations: 39264
% 17.10/8.42  #Strategies tried      : 1
% 17.10/8.42  
% 17.10/8.42  Timing (in seconds)
% 17.10/8.42  ----------------------
% 17.10/8.42  Preprocessing        : 0.35
% 17.10/8.42  Parsing              : 0.18
% 17.10/8.42  CNF conversion       : 0.03
% 17.10/8.42  Main loop            : 7.25
% 17.10/8.42  Inferencing          : 2.62
% 17.10/8.42  Reduction            : 2.31
% 17.10/8.42  Demodulation         : 1.84
% 17.10/8.42  BG Simplification    : 0.19
% 17.10/8.42  Subsumption          : 1.78
% 17.10/8.42  Abstraction          : 0.29
% 17.10/8.42  MUC search           : 0.00
% 17.10/8.42  Cooper               : 0.00
% 17.10/8.42  Total                : 7.63
% 17.10/8.42  Index Insertion      : 0.00
% 17.10/8.42  Index Deletion       : 0.00
% 17.10/8.42  Index Matching       : 0.00
% 17.10/8.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
