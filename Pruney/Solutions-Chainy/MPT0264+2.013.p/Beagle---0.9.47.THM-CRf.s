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
% DateTime   : Thu Dec  3 09:52:22 EST 2020

% Result     : Theorem 4.29s
% Output     : CNFRefutation 4.29s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 124 expanded)
%              Number of leaves         :   28 (  55 expanded)
%              Depth                    :   13
%              Number of atoms          :   90 ( 257 expanded)
%              Number of equality atoms :   26 (  64 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_7 > #skF_2 > #skF_6 > #skF_5 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k3_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
          & r2_hidden(B,C)
          & A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_zfmisc_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_54,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_52,axiom,(
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

tff(f_56,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,k3_xboole_0(A,B)),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_xboole_1)).

tff(f_84,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_76,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_78,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_54,plain,(
    ! [D_29,A_24] : r2_hidden(D_29,k2_tarski(A_24,D_29)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_80,plain,(
    k3_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_22,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_494,plain,(
    ! [A_91,C_92,B_93] :
      ( r2_hidden(A_91,C_92)
      | ~ r2_hidden(A_91,B_93)
      | r2_hidden(A_91,k5_xboole_0(B_93,C_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2589,plain,(
    ! [A_2941,A_2942,B_2943] :
      ( r2_hidden(A_2941,k3_xboole_0(A_2942,B_2943))
      | ~ r2_hidden(A_2941,A_2942)
      | r2_hidden(A_2941,k4_xboole_0(A_2942,B_2943)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_494])).

tff(c_20,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_1'(A_6,B_7),A_6)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_1'(A_6,B_7),B_7)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_24,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_26,plain,(
    ! [A_15,B_16] : r1_xboole_0(k4_xboole_0(A_15,k3_xboole_0(A_15,B_16)),B_16) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_81,plain,(
    ! [A_15,B_16] : r1_xboole_0(k4_xboole_0(A_15,B_16),B_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26])).

tff(c_298,plain,(
    ! [A_71,B_72,C_73] :
      ( ~ r1_xboole_0(A_71,B_72)
      | ~ r2_hidden(C_73,B_72)
      | ~ r2_hidden(C_73,A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_357,plain,(
    ! [C_76,B_77,A_78] :
      ( ~ r2_hidden(C_76,B_77)
      | ~ r2_hidden(C_76,k4_xboole_0(A_78,B_77)) ) ),
    inference(resolution,[status(thm)],[c_81,c_298])).

tff(c_841,plain,(
    ! [A_126,A_127,B_128] :
      ( ~ r2_hidden('#skF_1'(A_126,k4_xboole_0(A_127,B_128)),B_128)
      | r1_xboole_0(A_126,k4_xboole_0(A_127,B_128)) ) ),
    inference(resolution,[status(thm)],[c_18,c_357])).

tff(c_873,plain,(
    ! [A_129,A_130] : r1_xboole_0(A_129,k4_xboole_0(A_130,A_129)) ),
    inference(resolution,[status(thm)],[c_20,c_841])).

tff(c_16,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,B_7)
      | ~ r2_hidden(C_10,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_888,plain,(
    ! [C_10,A_130,A_129] :
      ( ~ r2_hidden(C_10,k4_xboole_0(A_130,A_129))
      | ~ r2_hidden(C_10,A_129) ) ),
    inference(resolution,[status(thm)],[c_873,c_16])).

tff(c_2671,plain,(
    ! [A_2976,B_2977,A_2978] :
      ( ~ r2_hidden(A_2976,B_2977)
      | r2_hidden(A_2976,k3_xboole_0(A_2978,B_2977))
      | ~ r2_hidden(A_2976,A_2978) ) ),
    inference(resolution,[status(thm)],[c_2589,c_888])).

tff(c_2743,plain,(
    ! [A_3011] :
      ( ~ r2_hidden(A_3011,'#skF_8')
      | r2_hidden(A_3011,k1_tarski('#skF_6'))
      | ~ r2_hidden(A_3011,k2_tarski('#skF_6','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_2671])).

tff(c_2759,plain,
    ( ~ r2_hidden('#skF_7','#skF_8')
    | r2_hidden('#skF_7',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_54,c_2743])).

tff(c_2768,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2759])).

tff(c_70,plain,(
    ! [A_30] : k2_tarski(A_30,A_30) = k1_tarski(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_91,plain,(
    ! [D_37,B_38] : r2_hidden(D_37,k2_tarski(D_37,B_38)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_94,plain,(
    ! [A_30] : r2_hidden(A_30,k1_tarski(A_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_91])).

tff(c_388,plain,(
    ! [D_82,B_83,A_84] :
      ( D_82 = B_83
      | D_82 = A_84
      | ~ r2_hidden(D_82,k2_tarski(A_84,B_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_412,plain,(
    ! [D_85,A_86] :
      ( D_85 = A_86
      | D_85 = A_86
      | ~ r2_hidden(D_85,k1_tarski(A_86)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_388])).

tff(c_490,plain,(
    ! [A_89,A_90] :
      ( '#skF_1'(A_89,k1_tarski(A_90)) = A_90
      | r1_xboole_0(A_89,k1_tarski(A_90)) ) ),
    inference(resolution,[status(thm)],[c_18,c_412])).

tff(c_1377,plain,(
    ! [C_181,A_182,A_183] :
      ( ~ r2_hidden(C_181,k1_tarski(A_182))
      | ~ r2_hidden(C_181,A_183)
      | '#skF_1'(A_183,k1_tarski(A_182)) = A_182 ) ),
    inference(resolution,[status(thm)],[c_490,c_16])).

tff(c_1389,plain,(
    ! [A_184,A_185] :
      ( ~ r2_hidden(A_184,A_185)
      | '#skF_1'(A_185,k1_tarski(A_184)) = A_184 ) ),
    inference(resolution,[status(thm)],[c_94,c_1377])).

tff(c_504,plain,(
    ! [A_94,B_95] :
      ( '#skF_1'(k1_tarski(A_94),B_95) = A_94
      | r1_xboole_0(k1_tarski(A_94),B_95) ) ),
    inference(resolution,[status(thm)],[c_20,c_412])).

tff(c_1250,plain,(
    ! [C_165,B_166,A_167] :
      ( ~ r2_hidden(C_165,B_166)
      | ~ r2_hidden(C_165,k1_tarski(A_167))
      | '#skF_1'(k1_tarski(A_167),B_166) = A_167 ) ),
    inference(resolution,[status(thm)],[c_504,c_16])).

tff(c_1281,plain,(
    ! [A_30,A_167] :
      ( ~ r2_hidden(A_30,k1_tarski(A_167))
      | '#skF_1'(k1_tarski(A_167),k1_tarski(A_30)) = A_167 ) ),
    inference(resolution,[status(thm)],[c_94,c_1250])).

tff(c_1396,plain,(
    ! [A_184,A_167] :
      ( ~ r2_hidden(A_184,k1_tarski(A_167))
      | A_184 = A_167
      | ~ r2_hidden(A_184,k1_tarski(A_167)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1389,c_1281])).

tff(c_2772,plain,
    ( '#skF_7' = '#skF_6'
    | ~ r2_hidden('#skF_7',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_2768,c_1396])).

tff(c_2785,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2768,c_2772])).

tff(c_2787,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2785])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:03:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.29/1.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.29/1.75  
% 4.29/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.29/1.76  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_7 > #skF_2 > #skF_6 > #skF_5 > #skF_8 > #skF_3 > #skF_1
% 4.29/1.76  
% 4.29/1.76  %Foreground sorts:
% 4.29/1.76  
% 4.29/1.76  
% 4.29/1.76  %Background operators:
% 4.29/1.76  
% 4.29/1.76  
% 4.29/1.76  %Foreground operators:
% 4.29/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.29/1.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.29/1.76  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.29/1.76  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.29/1.76  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.29/1.76  tff('#skF_7', type, '#skF_7': $i).
% 4.29/1.76  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.29/1.76  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.29/1.76  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.29/1.76  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.29/1.76  tff('#skF_6', type, '#skF_6': $i).
% 4.29/1.76  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 4.29/1.76  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.29/1.76  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.29/1.76  tff('#skF_8', type, '#skF_8': $i).
% 4.29/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.29/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.29/1.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.29/1.76  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.29/1.76  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.29/1.76  
% 4.29/1.77  tff(f_97, negated_conjecture, ~(![A, B, C]: ~(((k3_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) & r2_hidden(B, C)) & ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_zfmisc_1)).
% 4.29/1.77  tff(f_82, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 4.29/1.77  tff(f_54, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.29/1.77  tff(f_34, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 4.29/1.77  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.29/1.77  tff(f_56, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.29/1.77  tff(f_58, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, k3_xboole_0(A, B)), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_xboole_1)).
% 4.29/1.77  tff(f_84, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.29/1.77  tff(c_76, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.29/1.77  tff(c_78, plain, (r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.29/1.77  tff(c_54, plain, (![D_29, A_24]: (r2_hidden(D_29, k2_tarski(A_24, D_29)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.29/1.77  tff(c_80, plain, (k3_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.29/1.77  tff(c_22, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.29/1.77  tff(c_494, plain, (![A_91, C_92, B_93]: (r2_hidden(A_91, C_92) | ~r2_hidden(A_91, B_93) | r2_hidden(A_91, k5_xboole_0(B_93, C_92)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.29/1.77  tff(c_2589, plain, (![A_2941, A_2942, B_2943]: (r2_hidden(A_2941, k3_xboole_0(A_2942, B_2943)) | ~r2_hidden(A_2941, A_2942) | r2_hidden(A_2941, k4_xboole_0(A_2942, B_2943)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_494])).
% 4.29/1.77  tff(c_20, plain, (![A_6, B_7]: (r2_hidden('#skF_1'(A_6, B_7), A_6) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.29/1.77  tff(c_18, plain, (![A_6, B_7]: (r2_hidden('#skF_1'(A_6, B_7), B_7) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.29/1.77  tff(c_24, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.29/1.77  tff(c_26, plain, (![A_15, B_16]: (r1_xboole_0(k4_xboole_0(A_15, k3_xboole_0(A_15, B_16)), B_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.29/1.77  tff(c_81, plain, (![A_15, B_16]: (r1_xboole_0(k4_xboole_0(A_15, B_16), B_16))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26])).
% 4.29/1.77  tff(c_298, plain, (![A_71, B_72, C_73]: (~r1_xboole_0(A_71, B_72) | ~r2_hidden(C_73, B_72) | ~r2_hidden(C_73, A_71))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.29/1.77  tff(c_357, plain, (![C_76, B_77, A_78]: (~r2_hidden(C_76, B_77) | ~r2_hidden(C_76, k4_xboole_0(A_78, B_77)))), inference(resolution, [status(thm)], [c_81, c_298])).
% 4.29/1.77  tff(c_841, plain, (![A_126, A_127, B_128]: (~r2_hidden('#skF_1'(A_126, k4_xboole_0(A_127, B_128)), B_128) | r1_xboole_0(A_126, k4_xboole_0(A_127, B_128)))), inference(resolution, [status(thm)], [c_18, c_357])).
% 4.29/1.77  tff(c_873, plain, (![A_129, A_130]: (r1_xboole_0(A_129, k4_xboole_0(A_130, A_129)))), inference(resolution, [status(thm)], [c_20, c_841])).
% 4.29/1.77  tff(c_16, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, B_7) | ~r2_hidden(C_10, A_6))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.29/1.77  tff(c_888, plain, (![C_10, A_130, A_129]: (~r2_hidden(C_10, k4_xboole_0(A_130, A_129)) | ~r2_hidden(C_10, A_129))), inference(resolution, [status(thm)], [c_873, c_16])).
% 4.29/1.77  tff(c_2671, plain, (![A_2976, B_2977, A_2978]: (~r2_hidden(A_2976, B_2977) | r2_hidden(A_2976, k3_xboole_0(A_2978, B_2977)) | ~r2_hidden(A_2976, A_2978))), inference(resolution, [status(thm)], [c_2589, c_888])).
% 4.29/1.77  tff(c_2743, plain, (![A_3011]: (~r2_hidden(A_3011, '#skF_8') | r2_hidden(A_3011, k1_tarski('#skF_6')) | ~r2_hidden(A_3011, k2_tarski('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_80, c_2671])).
% 4.29/1.77  tff(c_2759, plain, (~r2_hidden('#skF_7', '#skF_8') | r2_hidden('#skF_7', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_2743])).
% 4.29/1.77  tff(c_2768, plain, (r2_hidden('#skF_7', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2759])).
% 4.29/1.77  tff(c_70, plain, (![A_30]: (k2_tarski(A_30, A_30)=k1_tarski(A_30))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.29/1.77  tff(c_91, plain, (![D_37, B_38]: (r2_hidden(D_37, k2_tarski(D_37, B_38)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.29/1.77  tff(c_94, plain, (![A_30]: (r2_hidden(A_30, k1_tarski(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_91])).
% 4.29/1.77  tff(c_388, plain, (![D_82, B_83, A_84]: (D_82=B_83 | D_82=A_84 | ~r2_hidden(D_82, k2_tarski(A_84, B_83)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.29/1.77  tff(c_412, plain, (![D_85, A_86]: (D_85=A_86 | D_85=A_86 | ~r2_hidden(D_85, k1_tarski(A_86)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_388])).
% 4.29/1.77  tff(c_490, plain, (![A_89, A_90]: ('#skF_1'(A_89, k1_tarski(A_90))=A_90 | r1_xboole_0(A_89, k1_tarski(A_90)))), inference(resolution, [status(thm)], [c_18, c_412])).
% 4.29/1.77  tff(c_1377, plain, (![C_181, A_182, A_183]: (~r2_hidden(C_181, k1_tarski(A_182)) | ~r2_hidden(C_181, A_183) | '#skF_1'(A_183, k1_tarski(A_182))=A_182)), inference(resolution, [status(thm)], [c_490, c_16])).
% 4.29/1.77  tff(c_1389, plain, (![A_184, A_185]: (~r2_hidden(A_184, A_185) | '#skF_1'(A_185, k1_tarski(A_184))=A_184)), inference(resolution, [status(thm)], [c_94, c_1377])).
% 4.29/1.77  tff(c_504, plain, (![A_94, B_95]: ('#skF_1'(k1_tarski(A_94), B_95)=A_94 | r1_xboole_0(k1_tarski(A_94), B_95))), inference(resolution, [status(thm)], [c_20, c_412])).
% 4.29/1.77  tff(c_1250, plain, (![C_165, B_166, A_167]: (~r2_hidden(C_165, B_166) | ~r2_hidden(C_165, k1_tarski(A_167)) | '#skF_1'(k1_tarski(A_167), B_166)=A_167)), inference(resolution, [status(thm)], [c_504, c_16])).
% 4.29/1.77  tff(c_1281, plain, (![A_30, A_167]: (~r2_hidden(A_30, k1_tarski(A_167)) | '#skF_1'(k1_tarski(A_167), k1_tarski(A_30))=A_167)), inference(resolution, [status(thm)], [c_94, c_1250])).
% 4.29/1.77  tff(c_1396, plain, (![A_184, A_167]: (~r2_hidden(A_184, k1_tarski(A_167)) | A_184=A_167 | ~r2_hidden(A_184, k1_tarski(A_167)))), inference(superposition, [status(thm), theory('equality')], [c_1389, c_1281])).
% 4.29/1.77  tff(c_2772, plain, ('#skF_7'='#skF_6' | ~r2_hidden('#skF_7', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_2768, c_1396])).
% 4.29/1.77  tff(c_2785, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2768, c_2772])).
% 4.29/1.77  tff(c_2787, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_2785])).
% 4.29/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.29/1.77  
% 4.29/1.77  Inference rules
% 4.29/1.77  ----------------------
% 4.29/1.77  #Ref     : 0
% 4.29/1.77  #Sup     : 486
% 4.29/1.77  #Fact    : 2
% 4.29/1.77  #Define  : 0
% 4.29/1.77  #Split   : 0
% 4.29/1.77  #Chain   : 0
% 4.29/1.77  #Close   : 0
% 4.29/1.77  
% 4.29/1.77  Ordering : KBO
% 4.29/1.77  
% 4.29/1.77  Simplification rules
% 4.29/1.77  ----------------------
% 4.29/1.77  #Subsume      : 50
% 4.29/1.77  #Demod        : 188
% 4.29/1.77  #Tautology    : 178
% 4.29/1.77  #SimpNegUnit  : 1
% 4.29/1.77  #BackRed      : 2
% 4.29/1.77  
% 4.29/1.77  #Partial instantiations: 1320
% 4.29/1.77  #Strategies tried      : 1
% 4.29/1.77  
% 4.29/1.77  Timing (in seconds)
% 4.29/1.77  ----------------------
% 4.29/1.77  Preprocessing        : 0.33
% 4.29/1.77  Parsing              : 0.17
% 4.29/1.77  CNF conversion       : 0.02
% 4.29/1.77  Main loop            : 0.69
% 4.29/1.77  Inferencing          : 0.27
% 4.29/1.77  Reduction            : 0.24
% 4.29/1.77  Demodulation         : 0.19
% 4.29/1.77  BG Simplification    : 0.03
% 4.29/1.77  Subsumption          : 0.11
% 4.29/1.77  Abstraction          : 0.03
% 4.29/1.77  MUC search           : 0.00
% 4.29/1.77  Cooper               : 0.00
% 4.29/1.77  Total                : 1.05
% 4.29/1.77  Index Insertion      : 0.00
% 4.29/1.77  Index Deletion       : 0.00
% 4.29/1.77  Index Matching       : 0.00
% 4.29/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
