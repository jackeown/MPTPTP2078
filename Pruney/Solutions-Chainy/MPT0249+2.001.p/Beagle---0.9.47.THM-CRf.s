%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:23 EST 2020

% Result     : Theorem 13.64s
% Output     : CNFRefutation 13.64s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 209 expanded)
%              Number of leaves         :   34 (  86 expanded)
%              Depth                    :   12
%              Number of atoms          :  102 ( 337 expanded)
%              Number of equality atoms :   45 ( 181 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_106,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_77,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_46,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_93,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_70,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_72,plain,(
    k2_xboole_0('#skF_6','#skF_7') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_114,plain,(
    ! [A_73,B_74] : r1_tarski(A_73,k2_xboole_0(A_73,B_74)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_117,plain,(
    r1_tarski('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_114])).

tff(c_363,plain,(
    ! [B_96,A_97] :
      ( B_96 = A_97
      | ~ r1_tarski(B_96,A_97)
      | ~ r1_tarski(A_97,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_373,plain,
    ( k1_tarski('#skF_5') = '#skF_6'
    | ~ r1_tarski(k1_tarski('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_117,c_363])).

tff(c_400,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_373])).

tff(c_422,plain,(
    ! [A_101,B_102] :
      ( r2_hidden('#skF_1'(A_101,B_102),A_101)
      | r1_tarski(A_101,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_38,plain,(
    ! [C_36,A_32] :
      ( C_36 = A_32
      | ~ r2_hidden(C_36,k1_tarski(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6171,plain,(
    ! [A_6263,B_6264] :
      ( '#skF_1'(k1_tarski(A_6263),B_6264) = A_6263
      | r1_tarski(k1_tarski(A_6263),B_6264) ) ),
    inference(resolution,[status(thm)],[c_422,c_38])).

tff(c_6264,plain,(
    '#skF_1'(k1_tarski('#skF_5'),'#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_6171,c_400])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6270,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | r1_tarski(k1_tarski('#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_6264,c_6])).

tff(c_6320,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_400,c_6270])).

tff(c_14,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_2'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_691,plain,(
    ! [C_118,B_119,A_120] :
      ( r2_hidden(C_118,B_119)
      | ~ r2_hidden(C_118,A_120)
      | ~ r1_tarski(A_120,B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6527,plain,(
    ! [A_6631,B_6632] :
      ( r2_hidden('#skF_2'(A_6631),B_6632)
      | ~ r1_tarski(A_6631,B_6632)
      | k1_xboole_0 = A_6631 ) ),
    inference(resolution,[status(thm)],[c_14,c_691])).

tff(c_25853,plain,(
    ! [A_12185,A_12186] :
      ( A_12185 = '#skF_2'(A_12186)
      | ~ r1_tarski(A_12186,k1_tarski(A_12185))
      | k1_xboole_0 = A_12186 ) ),
    inference(resolution,[status(thm)],[c_6527,c_38])).

tff(c_25867,plain,
    ( '#skF_2'('#skF_6') = '#skF_5'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_117,c_25853])).

tff(c_25878,plain,(
    '#skF_2'('#skF_6') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_25867])).

tff(c_25886,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_25878,c_14])).

tff(c_25891,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_6320,c_25886])).

tff(c_25892,plain,(
    k1_tarski('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_373])).

tff(c_36,plain,(
    ! [B_31,A_30] : k2_tarski(B_31,A_30) = k2_tarski(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_231,plain,(
    ! [A_86,B_87] : k3_tarski(k2_tarski(A_86,B_87)) = k2_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_273,plain,(
    ! [B_90,A_91] : k3_tarski(k2_tarski(B_90,A_91)) = k2_xboole_0(A_91,B_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_231])).

tff(c_64,plain,(
    ! [A_65,B_66] : k3_tarski(k2_tarski(A_65,B_66)) = k2_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_300,plain,(
    ! [B_92,A_93] : k2_xboole_0(B_92,A_93) = k2_xboole_0(A_93,B_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_64])).

tff(c_28,plain,(
    ! [A_22,B_23] : r1_tarski(A_22,k2_xboole_0(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_339,plain,(
    ! [A_94,B_95] : r1_tarski(A_94,k2_xboole_0(B_95,A_94)) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_28])).

tff(c_354,plain,(
    r1_tarski('#skF_7',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_339])).

tff(c_25895,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25892,c_354])).

tff(c_16,plain,(
    ! [B_15,A_14] :
      ( B_15 = A_14
      | ~ r1_tarski(B_15,A_14)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_25933,plain,
    ( '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_25895,c_16])).

tff(c_25939,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_25933])).

tff(c_26028,plain,(
    ! [A_12294,B_12295] :
      ( r2_hidden('#skF_1'(A_12294,B_12295),A_12294)
      | r1_tarski(A_12294,B_12295) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_25910,plain,(
    ! [C_36] :
      ( C_36 = '#skF_5'
      | ~ r2_hidden(C_36,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25892,c_38])).

tff(c_26039,plain,(
    ! [B_12296] :
      ( '#skF_1'('#skF_6',B_12296) = '#skF_5'
      | r1_tarski('#skF_6',B_12296) ) ),
    inference(resolution,[status(thm)],[c_26028,c_25910])).

tff(c_26048,plain,(
    '#skF_1'('#skF_6','#skF_7') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_26039,c_25939])).

tff(c_26060,plain,(
    ! [A_12297,B_12298] :
      ( ~ r2_hidden('#skF_1'(A_12297,B_12298),B_12298)
      | r1_tarski(A_12297,B_12298) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_26063,plain,
    ( ~ r2_hidden('#skF_5','#skF_7')
    | r1_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_26048,c_26060])).

tff(c_26068,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_25939,c_26063])).

tff(c_26847,plain,(
    ! [C_12324,B_12325,A_12326] :
      ( r2_hidden(C_12324,B_12325)
      | ~ r2_hidden(C_12324,A_12326)
      | ~ r1_tarski(A_12326,B_12325) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_29758,plain,(
    ! [A_17760,B_17761] :
      ( r2_hidden('#skF_2'(A_17760),B_17761)
      | ~ r1_tarski(A_17760,B_17761)
      | k1_xboole_0 = A_17760 ) ),
    inference(resolution,[status(thm)],[c_14,c_26847])).

tff(c_30540,plain,(
    ! [A_18292] :
      ( '#skF_2'(A_18292) = '#skF_5'
      | ~ r1_tarski(A_18292,'#skF_6')
      | k1_xboole_0 = A_18292 ) ),
    inference(resolution,[status(thm)],[c_29758,c_25910])).

tff(c_30547,plain,
    ( '#skF_2'('#skF_7') = '#skF_5'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_25895,c_30540])).

tff(c_30557,plain,(
    '#skF_2'('#skF_7') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_30547])).

tff(c_30567,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_30557,c_14])).

tff(c_30572,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_26068,c_30567])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:49:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.64/5.91  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.64/5.92  
% 13.64/5.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.64/5.92  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4
% 13.64/5.92  
% 13.64/5.92  %Foreground sorts:
% 13.64/5.92  
% 13.64/5.92  
% 13.64/5.92  %Background operators:
% 13.64/5.92  
% 13.64/5.92  
% 13.64/5.92  %Foreground operators:
% 13.64/5.92  tff('#skF_2', type, '#skF_2': $i > $i).
% 13.64/5.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.64/5.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.64/5.92  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.64/5.92  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.64/5.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.64/5.92  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 13.64/5.92  tff('#skF_7', type, '#skF_7': $i).
% 13.64/5.92  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 13.64/5.92  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 13.64/5.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.64/5.92  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.64/5.92  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.64/5.92  tff('#skF_5', type, '#skF_5': $i).
% 13.64/5.92  tff('#skF_6', type, '#skF_6': $i).
% 13.64/5.92  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.64/5.92  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 13.64/5.92  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 13.64/5.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.64/5.92  tff(k3_tarski, type, k3_tarski: $i > $i).
% 13.64/5.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.64/5.92  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.64/5.92  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.64/5.92  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 13.64/5.92  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.64/5.92  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 13.64/5.92  
% 13.64/5.94  tff(f_106, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 13.64/5.94  tff(f_62, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 13.64/5.94  tff(f_52, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.64/5.94  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 13.64/5.94  tff(f_77, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 13.64/5.94  tff(f_46, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 13.64/5.94  tff(f_70, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 13.64/5.94  tff(f_93, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 13.64/5.94  tff(c_66, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_106])).
% 13.64/5.94  tff(c_70, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_106])).
% 13.64/5.94  tff(c_68, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_106])).
% 13.64/5.94  tff(c_72, plain, (k2_xboole_0('#skF_6', '#skF_7')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 13.64/5.94  tff(c_114, plain, (![A_73, B_74]: (r1_tarski(A_73, k2_xboole_0(A_73, B_74)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 13.64/5.94  tff(c_117, plain, (r1_tarski('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_114])).
% 13.64/5.94  tff(c_363, plain, (![B_96, A_97]: (B_96=A_97 | ~r1_tarski(B_96, A_97) | ~r1_tarski(A_97, B_96))), inference(cnfTransformation, [status(thm)], [f_52])).
% 13.64/5.94  tff(c_373, plain, (k1_tarski('#skF_5')='#skF_6' | ~r1_tarski(k1_tarski('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_117, c_363])).
% 13.64/5.94  tff(c_400, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_373])).
% 13.64/5.94  tff(c_422, plain, (![A_101, B_102]: (r2_hidden('#skF_1'(A_101, B_102), A_101) | r1_tarski(A_101, B_102))), inference(cnfTransformation, [status(thm)], [f_34])).
% 13.64/5.94  tff(c_38, plain, (![C_36, A_32]: (C_36=A_32 | ~r2_hidden(C_36, k1_tarski(A_32)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 13.64/5.94  tff(c_6171, plain, (![A_6263, B_6264]: ('#skF_1'(k1_tarski(A_6263), B_6264)=A_6263 | r1_tarski(k1_tarski(A_6263), B_6264))), inference(resolution, [status(thm)], [c_422, c_38])).
% 13.64/5.94  tff(c_6264, plain, ('#skF_1'(k1_tarski('#skF_5'), '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_6171, c_400])).
% 13.64/5.94  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 13.64/5.94  tff(c_6270, plain, (~r2_hidden('#skF_5', '#skF_6') | r1_tarski(k1_tarski('#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_6264, c_6])).
% 13.64/5.94  tff(c_6320, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_400, c_6270])).
% 13.64/5.94  tff(c_14, plain, (![A_12]: (r2_hidden('#skF_2'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_46])).
% 13.64/5.94  tff(c_691, plain, (![C_118, B_119, A_120]: (r2_hidden(C_118, B_119) | ~r2_hidden(C_118, A_120) | ~r1_tarski(A_120, B_119))), inference(cnfTransformation, [status(thm)], [f_34])).
% 13.64/5.94  tff(c_6527, plain, (![A_6631, B_6632]: (r2_hidden('#skF_2'(A_6631), B_6632) | ~r1_tarski(A_6631, B_6632) | k1_xboole_0=A_6631)), inference(resolution, [status(thm)], [c_14, c_691])).
% 13.64/5.94  tff(c_25853, plain, (![A_12185, A_12186]: (A_12185='#skF_2'(A_12186) | ~r1_tarski(A_12186, k1_tarski(A_12185)) | k1_xboole_0=A_12186)), inference(resolution, [status(thm)], [c_6527, c_38])).
% 13.64/5.94  tff(c_25867, plain, ('#skF_2'('#skF_6')='#skF_5' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_117, c_25853])).
% 13.64/5.94  tff(c_25878, plain, ('#skF_2'('#skF_6')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_68, c_25867])).
% 13.64/5.94  tff(c_25886, plain, (r2_hidden('#skF_5', '#skF_6') | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_25878, c_14])).
% 13.64/5.94  tff(c_25891, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_6320, c_25886])).
% 13.64/5.94  tff(c_25892, plain, (k1_tarski('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_373])).
% 13.64/5.94  tff(c_36, plain, (![B_31, A_30]: (k2_tarski(B_31, A_30)=k2_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_70])).
% 13.64/5.94  tff(c_231, plain, (![A_86, B_87]: (k3_tarski(k2_tarski(A_86, B_87))=k2_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_93])).
% 13.64/5.94  tff(c_273, plain, (![B_90, A_91]: (k3_tarski(k2_tarski(B_90, A_91))=k2_xboole_0(A_91, B_90))), inference(superposition, [status(thm), theory('equality')], [c_36, c_231])).
% 13.64/5.94  tff(c_64, plain, (![A_65, B_66]: (k3_tarski(k2_tarski(A_65, B_66))=k2_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_93])).
% 13.64/5.94  tff(c_300, plain, (![B_92, A_93]: (k2_xboole_0(B_92, A_93)=k2_xboole_0(A_93, B_92))), inference(superposition, [status(thm), theory('equality')], [c_273, c_64])).
% 13.64/5.94  tff(c_28, plain, (![A_22, B_23]: (r1_tarski(A_22, k2_xboole_0(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 13.64/5.94  tff(c_339, plain, (![A_94, B_95]: (r1_tarski(A_94, k2_xboole_0(B_95, A_94)))), inference(superposition, [status(thm), theory('equality')], [c_300, c_28])).
% 13.64/5.94  tff(c_354, plain, (r1_tarski('#skF_7', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_339])).
% 13.64/5.94  tff(c_25895, plain, (r1_tarski('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_25892, c_354])).
% 13.64/5.94  tff(c_16, plain, (![B_15, A_14]: (B_15=A_14 | ~r1_tarski(B_15, A_14) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_52])).
% 13.64/5.94  tff(c_25933, plain, ('#skF_7'='#skF_6' | ~r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_25895, c_16])).
% 13.64/5.94  tff(c_25939, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_70, c_25933])).
% 13.64/5.94  tff(c_26028, plain, (![A_12294, B_12295]: (r2_hidden('#skF_1'(A_12294, B_12295), A_12294) | r1_tarski(A_12294, B_12295))), inference(cnfTransformation, [status(thm)], [f_34])).
% 13.64/5.94  tff(c_25910, plain, (![C_36]: (C_36='#skF_5' | ~r2_hidden(C_36, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_25892, c_38])).
% 13.64/5.94  tff(c_26039, plain, (![B_12296]: ('#skF_1'('#skF_6', B_12296)='#skF_5' | r1_tarski('#skF_6', B_12296))), inference(resolution, [status(thm)], [c_26028, c_25910])).
% 13.64/5.94  tff(c_26048, plain, ('#skF_1'('#skF_6', '#skF_7')='#skF_5'), inference(resolution, [status(thm)], [c_26039, c_25939])).
% 13.64/5.94  tff(c_26060, plain, (![A_12297, B_12298]: (~r2_hidden('#skF_1'(A_12297, B_12298), B_12298) | r1_tarski(A_12297, B_12298))), inference(cnfTransformation, [status(thm)], [f_34])).
% 13.64/5.94  tff(c_26063, plain, (~r2_hidden('#skF_5', '#skF_7') | r1_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_26048, c_26060])).
% 13.64/5.94  tff(c_26068, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_25939, c_26063])).
% 13.64/5.94  tff(c_26847, plain, (![C_12324, B_12325, A_12326]: (r2_hidden(C_12324, B_12325) | ~r2_hidden(C_12324, A_12326) | ~r1_tarski(A_12326, B_12325))), inference(cnfTransformation, [status(thm)], [f_34])).
% 13.64/5.94  tff(c_29758, plain, (![A_17760, B_17761]: (r2_hidden('#skF_2'(A_17760), B_17761) | ~r1_tarski(A_17760, B_17761) | k1_xboole_0=A_17760)), inference(resolution, [status(thm)], [c_14, c_26847])).
% 13.64/5.94  tff(c_30540, plain, (![A_18292]: ('#skF_2'(A_18292)='#skF_5' | ~r1_tarski(A_18292, '#skF_6') | k1_xboole_0=A_18292)), inference(resolution, [status(thm)], [c_29758, c_25910])).
% 13.64/5.94  tff(c_30547, plain, ('#skF_2'('#skF_7')='#skF_5' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_25895, c_30540])).
% 13.64/5.94  tff(c_30557, plain, ('#skF_2'('#skF_7')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_66, c_30547])).
% 13.64/5.94  tff(c_30567, plain, (r2_hidden('#skF_5', '#skF_7') | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_30557, c_14])).
% 13.64/5.94  tff(c_30572, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_26068, c_30567])).
% 13.64/5.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.64/5.94  
% 13.64/5.94  Inference rules
% 13.64/5.94  ----------------------
% 13.64/5.94  #Ref     : 0
% 13.64/5.94  #Sup     : 6752
% 13.64/5.94  #Fact    : 8
% 13.64/5.94  #Define  : 0
% 13.64/5.94  #Split   : 8
% 13.64/5.94  #Chain   : 0
% 13.64/5.94  #Close   : 0
% 13.64/5.94  
% 13.64/5.94  Ordering : KBO
% 13.64/5.94  
% 13.64/5.94  Simplification rules
% 13.64/5.94  ----------------------
% 13.64/5.94  #Subsume      : 360
% 13.64/5.94  #Demod        : 8814
% 13.64/5.94  #Tautology    : 3921
% 13.64/5.94  #SimpNegUnit  : 38
% 13.64/5.94  #BackRed      : 15
% 13.64/5.94  
% 13.64/5.94  #Partial instantiations: 7203
% 13.64/5.94  #Strategies tried      : 1
% 13.64/5.94  
% 13.64/5.94  Timing (in seconds)
% 13.64/5.94  ----------------------
% 13.64/5.94  Preprocessing        : 0.40
% 13.64/5.94  Parsing              : 0.18
% 13.64/5.94  CNF conversion       : 0.03
% 13.64/5.94  Main loop            : 4.75
% 13.64/5.94  Inferencing          : 0.99
% 13.64/5.94  Reduction            : 2.80
% 13.64/5.94  Demodulation         : 2.53
% 13.64/5.94  BG Simplification    : 0.11
% 13.64/5.94  Subsumption          : 0.63
% 13.64/5.94  Abstraction          : 0.16
% 13.64/5.94  MUC search           : 0.00
% 13.64/5.94  Cooper               : 0.00
% 13.64/5.94  Total                : 5.18
% 13.64/5.94  Index Insertion      : 0.00
% 13.64/5.94  Index Deletion       : 0.00
% 13.64/5.94  Index Matching       : 0.00
% 13.64/5.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
