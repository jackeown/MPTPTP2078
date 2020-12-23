%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:18 EST 2020

% Result     : Theorem 5.91s
% Output     : CNFRefutation 6.02s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 178 expanded)
%              Number of leaves         :   28 (  69 expanded)
%              Depth                    :    9
%              Number of atoms          :  127 ( 371 expanded)
%              Number of equality atoms :   21 (  81 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

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

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_50,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_54,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_77,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_91,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_86,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_69,plain,(
    ! [A_34] : k2_tarski(A_34,A_34) = k1_tarski(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_24,plain,(
    ! [D_14,A_9] : r2_hidden(D_14,k2_tarski(A_9,D_14)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_75,plain,(
    ! [A_34] : r2_hidden(A_34,k1_tarski(A_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_24])).

tff(c_44,plain,(
    ! [A_18] : k2_xboole_0(A_18,k1_tarski(A_18)) = k1_ordinal1(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_147,plain,(
    ! [D_53,B_54,A_55] :
      ( ~ r2_hidden(D_53,B_54)
      | r2_hidden(D_53,k2_xboole_0(A_55,B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1339,plain,(
    ! [D_137,A_138] :
      ( ~ r2_hidden(D_137,k1_tarski(A_138))
      | r2_hidden(D_137,k1_ordinal1(A_138)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_147])).

tff(c_1358,plain,(
    ! [A_34] : r2_hidden(A_34,k1_ordinal1(A_34)) ),
    inference(resolution,[status(thm)],[c_75,c_1339])).

tff(c_58,plain,(
    v3_ordinal1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_56,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_60,plain,
    ( ~ r1_ordinal1('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_108,plain,(
    ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_66,plain,
    ( r2_hidden('#skF_5',k1_ordinal1('#skF_6'))
    | r1_ordinal1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_128,plain,(
    r1_ordinal1('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_66])).

tff(c_48,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,B_20)
      | ~ r1_ordinal1(A_19,B_20)
      | ~ v3_ordinal1(B_20)
      | ~ v3_ordinal1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_920,plain,(
    ! [B_129,A_130] :
      ( r2_hidden(B_129,A_130)
      | B_129 = A_130
      | r2_hidden(A_130,B_129)
      | ~ v3_ordinal1(B_129)
      | ~ v3_ordinal1(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_209,plain,(
    ! [D_65,A_66,B_67] :
      ( ~ r2_hidden(D_65,A_66)
      | r2_hidden(D_65,k2_xboole_0(A_66,B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_275,plain,(
    ! [D_71,A_72] :
      ( ~ r2_hidden(D_71,A_72)
      | r2_hidden(D_71,k1_ordinal1(A_72)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_209])).

tff(c_325,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_275,c_108])).

tff(c_1004,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_920,c_325])).

tff(c_1194,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_1004])).

tff(c_1247,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1194])).

tff(c_54,plain,(
    ! [B_28,A_27] :
      ( ~ r1_tarski(B_28,A_27)
      | ~ r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1254,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_1247,c_54])).

tff(c_1257,plain,
    ( ~ r1_ordinal1('#skF_5','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_1254])).

tff(c_1261,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_128,c_1257])).

tff(c_1262,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1194])).

tff(c_1267,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1262,c_108])).

tff(c_1361,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1358,c_1267])).

tff(c_1362,plain,(
    ~ r1_ordinal1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1363,plain,(
    r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_2022,plain,(
    ! [D_213,B_214,A_215] :
      ( r2_hidden(D_213,B_214)
      | r2_hidden(D_213,A_215)
      | ~ r2_hidden(D_213,k2_xboole_0(A_215,B_214)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5255,plain,(
    ! [D_412,A_413] :
      ( r2_hidden(D_412,k1_tarski(A_413))
      | r2_hidden(D_412,A_413)
      | ~ r2_hidden(D_412,k1_ordinal1(A_413)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_2022])).

tff(c_40,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1540,plain,(
    ! [D_167,B_168,A_169] :
      ( D_167 = B_168
      | D_167 = A_169
      | ~ r2_hidden(D_167,k2_tarski(A_169,B_168)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1543,plain,(
    ! [D_167,A_15] :
      ( D_167 = A_15
      | D_167 = A_15
      | ~ r2_hidden(D_167,k1_tarski(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1540])).

tff(c_6006,plain,(
    ! [D_428,A_429] :
      ( D_428 = A_429
      | r2_hidden(D_428,A_429)
      | ~ r2_hidden(D_428,k1_ordinal1(A_429)) ) ),
    inference(resolution,[status(thm)],[c_5255,c_1543])).

tff(c_6079,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_1363,c_6006])).

tff(c_6080,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_6079])).

tff(c_1610,plain,(
    ! [B_175,A_176] :
      ( r2_hidden(B_175,A_176)
      | r1_ordinal1(A_176,B_175)
      | ~ v3_ordinal1(B_175)
      | ~ v3_ordinal1(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_1676,plain,(
    ! [A_176,B_175] :
      ( ~ r2_hidden(A_176,B_175)
      | r1_ordinal1(A_176,B_175)
      | ~ v3_ordinal1(B_175)
      | ~ v3_ordinal1(A_176) ) ),
    inference(resolution,[status(thm)],[c_1610,c_2])).

tff(c_6083,plain,
    ( r1_ordinal1('#skF_5','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_6080,c_1676])).

tff(c_6091,plain,(
    r1_ordinal1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_6083])).

tff(c_6093,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1362,c_6091])).

tff(c_6094,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_6079])).

tff(c_6642,plain,(
    ~ r1_ordinal1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6094,c_1362])).

tff(c_52,plain,(
    ! [B_26,A_24] :
      ( r2_hidden(B_26,A_24)
      | r1_ordinal1(A_24,B_26)
      | ~ v3_ordinal1(B_26)
      | ~ v3_ordinal1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_6095,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_6079])).

tff(c_6650,plain,(
    ~ r2_hidden('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6094,c_6095])).

tff(c_6658,plain,
    ( r1_ordinal1('#skF_6','#skF_6')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_6650])).

tff(c_6665,plain,(
    r1_ordinal1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_6658])).

tff(c_6666,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6642,c_6665])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:59:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.91/2.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.91/2.16  
% 5.91/2.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.91/2.16  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 5.91/2.16  
% 5.91/2.16  %Foreground sorts:
% 5.91/2.16  
% 5.91/2.16  
% 5.91/2.16  %Background operators:
% 5.91/2.16  
% 5.91/2.16  
% 5.91/2.16  %Foreground operators:
% 5.91/2.16  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.91/2.16  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 5.91/2.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.91/2.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.91/2.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.91/2.16  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.91/2.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.91/2.16  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 5.91/2.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.91/2.16  tff('#skF_5', type, '#skF_5': $i).
% 5.91/2.16  tff('#skF_6', type, '#skF_6': $i).
% 5.91/2.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.91/2.16  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.91/2.16  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 5.91/2.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.91/2.16  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.91/2.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.91/2.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.91/2.16  
% 6.02/2.18  tff(f_50, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.02/2.18  tff(f_48, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 6.02/2.18  tff(f_54, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 6.02/2.18  tff(f_39, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 6.02/2.18  tff(f_101, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 6.02/2.18  tff(f_62, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 6.02/2.18  tff(f_77, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 6.02/2.18  tff(f_91, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.02/2.18  tff(f_86, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 6.02/2.18  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 6.02/2.18  tff(c_69, plain, (![A_34]: (k2_tarski(A_34, A_34)=k1_tarski(A_34))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.02/2.18  tff(c_24, plain, (![D_14, A_9]: (r2_hidden(D_14, k2_tarski(A_9, D_14)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.02/2.18  tff(c_75, plain, (![A_34]: (r2_hidden(A_34, k1_tarski(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_69, c_24])).
% 6.02/2.18  tff(c_44, plain, (![A_18]: (k2_xboole_0(A_18, k1_tarski(A_18))=k1_ordinal1(A_18))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.02/2.18  tff(c_147, plain, (![D_53, B_54, A_55]: (~r2_hidden(D_53, B_54) | r2_hidden(D_53, k2_xboole_0(A_55, B_54)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.02/2.18  tff(c_1339, plain, (![D_137, A_138]: (~r2_hidden(D_137, k1_tarski(A_138)) | r2_hidden(D_137, k1_ordinal1(A_138)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_147])).
% 6.02/2.18  tff(c_1358, plain, (![A_34]: (r2_hidden(A_34, k1_ordinal1(A_34)))), inference(resolution, [status(thm)], [c_75, c_1339])).
% 6.02/2.18  tff(c_58, plain, (v3_ordinal1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.02/2.18  tff(c_56, plain, (v3_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.02/2.18  tff(c_60, plain, (~r1_ordinal1('#skF_5', '#skF_6') | ~r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.02/2.18  tff(c_108, plain, (~r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(splitLeft, [status(thm)], [c_60])).
% 6.02/2.18  tff(c_66, plain, (r2_hidden('#skF_5', k1_ordinal1('#skF_6')) | r1_ordinal1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.02/2.18  tff(c_128, plain, (r1_ordinal1('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_108, c_66])).
% 6.02/2.18  tff(c_48, plain, (![A_19, B_20]: (r1_tarski(A_19, B_20) | ~r1_ordinal1(A_19, B_20) | ~v3_ordinal1(B_20) | ~v3_ordinal1(A_19))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.02/2.18  tff(c_920, plain, (![B_129, A_130]: (r2_hidden(B_129, A_130) | B_129=A_130 | r2_hidden(A_130, B_129) | ~v3_ordinal1(B_129) | ~v3_ordinal1(A_130))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.02/2.18  tff(c_209, plain, (![D_65, A_66, B_67]: (~r2_hidden(D_65, A_66) | r2_hidden(D_65, k2_xboole_0(A_66, B_67)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.02/2.18  tff(c_275, plain, (![D_71, A_72]: (~r2_hidden(D_71, A_72) | r2_hidden(D_71, k1_ordinal1(A_72)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_209])).
% 6.02/2.18  tff(c_325, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_275, c_108])).
% 6.02/2.18  tff(c_1004, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_920, c_325])).
% 6.02/2.18  tff(c_1194, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_1004])).
% 6.02/2.18  tff(c_1247, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_1194])).
% 6.02/2.18  tff(c_54, plain, (![B_28, A_27]: (~r1_tarski(B_28, A_27) | ~r2_hidden(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.02/2.18  tff(c_1254, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_1247, c_54])).
% 6.02/2.18  tff(c_1257, plain, (~r1_ordinal1('#skF_5', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_1254])).
% 6.02/2.18  tff(c_1261, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_128, c_1257])).
% 6.02/2.18  tff(c_1262, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_1194])).
% 6.02/2.18  tff(c_1267, plain, (~r2_hidden('#skF_6', k1_ordinal1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1262, c_108])).
% 6.02/2.18  tff(c_1361, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1358, c_1267])).
% 6.02/2.18  tff(c_1362, plain, (~r1_ordinal1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_60])).
% 6.02/2.18  tff(c_1363, plain, (r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(splitRight, [status(thm)], [c_60])).
% 6.02/2.18  tff(c_2022, plain, (![D_213, B_214, A_215]: (r2_hidden(D_213, B_214) | r2_hidden(D_213, A_215) | ~r2_hidden(D_213, k2_xboole_0(A_215, B_214)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.02/2.18  tff(c_5255, plain, (![D_412, A_413]: (r2_hidden(D_412, k1_tarski(A_413)) | r2_hidden(D_412, A_413) | ~r2_hidden(D_412, k1_ordinal1(A_413)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_2022])).
% 6.02/2.18  tff(c_40, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.02/2.18  tff(c_1540, plain, (![D_167, B_168, A_169]: (D_167=B_168 | D_167=A_169 | ~r2_hidden(D_167, k2_tarski(A_169, B_168)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.02/2.18  tff(c_1543, plain, (![D_167, A_15]: (D_167=A_15 | D_167=A_15 | ~r2_hidden(D_167, k1_tarski(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1540])).
% 6.02/2.18  tff(c_6006, plain, (![D_428, A_429]: (D_428=A_429 | r2_hidden(D_428, A_429) | ~r2_hidden(D_428, k1_ordinal1(A_429)))), inference(resolution, [status(thm)], [c_5255, c_1543])).
% 6.02/2.18  tff(c_6079, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_1363, c_6006])).
% 6.02/2.18  tff(c_6080, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_6079])).
% 6.02/2.18  tff(c_1610, plain, (![B_175, A_176]: (r2_hidden(B_175, A_176) | r1_ordinal1(A_176, B_175) | ~v3_ordinal1(B_175) | ~v3_ordinal1(A_176))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.02/2.18  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 6.02/2.18  tff(c_1676, plain, (![A_176, B_175]: (~r2_hidden(A_176, B_175) | r1_ordinal1(A_176, B_175) | ~v3_ordinal1(B_175) | ~v3_ordinal1(A_176))), inference(resolution, [status(thm)], [c_1610, c_2])).
% 6.02/2.18  tff(c_6083, plain, (r1_ordinal1('#skF_5', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_6080, c_1676])).
% 6.02/2.18  tff(c_6091, plain, (r1_ordinal1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_6083])).
% 6.02/2.18  tff(c_6093, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1362, c_6091])).
% 6.02/2.18  tff(c_6094, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_6079])).
% 6.02/2.18  tff(c_6642, plain, (~r1_ordinal1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6094, c_1362])).
% 6.02/2.18  tff(c_52, plain, (![B_26, A_24]: (r2_hidden(B_26, A_24) | r1_ordinal1(A_24, B_26) | ~v3_ordinal1(B_26) | ~v3_ordinal1(A_24))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.02/2.18  tff(c_6095, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_6079])).
% 6.02/2.18  tff(c_6650, plain, (~r2_hidden('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6094, c_6095])).
% 6.02/2.18  tff(c_6658, plain, (r1_ordinal1('#skF_6', '#skF_6') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_6650])).
% 6.02/2.18  tff(c_6665, plain, (r1_ordinal1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_6658])).
% 6.02/2.18  tff(c_6666, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6642, c_6665])).
% 6.02/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.02/2.18  
% 6.02/2.18  Inference rules
% 6.02/2.18  ----------------------
% 6.02/2.18  #Ref     : 0
% 6.02/2.18  #Sup     : 1343
% 6.02/2.18  #Fact    : 10
% 6.02/2.18  #Define  : 0
% 6.02/2.18  #Split   : 5
% 6.02/2.18  #Chain   : 0
% 6.02/2.18  #Close   : 0
% 6.02/2.18  
% 6.02/2.18  Ordering : KBO
% 6.02/2.18  
% 6.02/2.18  Simplification rules
% 6.02/2.18  ----------------------
% 6.02/2.18  #Subsume      : 167
% 6.02/2.18  #Demod        : 60
% 6.02/2.18  #Tautology    : 64
% 6.02/2.18  #SimpNegUnit  : 20
% 6.02/2.18  #BackRed      : 11
% 6.02/2.18  
% 6.02/2.18  #Partial instantiations: 0
% 6.02/2.18  #Strategies tried      : 1
% 6.02/2.18  
% 6.02/2.18  Timing (in seconds)
% 6.02/2.18  ----------------------
% 6.02/2.18  Preprocessing        : 0.32
% 6.02/2.18  Parsing              : 0.16
% 6.02/2.18  CNF conversion       : 0.02
% 6.02/2.18  Main loop            : 1.10
% 6.02/2.18  Inferencing          : 0.32
% 6.02/2.18  Reduction            : 0.31
% 6.02/2.18  Demodulation         : 0.18
% 6.02/2.18  BG Simplification    : 0.05
% 6.02/2.18  Subsumption          : 0.31
% 6.02/2.18  Abstraction          : 0.06
% 6.02/2.18  MUC search           : 0.00
% 6.02/2.18  Cooper               : 0.00
% 6.02/2.18  Total                : 1.45
% 6.02/2.18  Index Insertion      : 0.00
% 6.02/2.18  Index Deletion       : 0.00
% 6.02/2.18  Index Matching       : 0.00
% 6.02/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
