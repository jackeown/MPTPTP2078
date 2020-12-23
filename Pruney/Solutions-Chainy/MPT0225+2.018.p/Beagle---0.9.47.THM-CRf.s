%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:33 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 125 expanded)
%              Number of leaves         :   33 (  57 expanded)
%              Depth                    :    6
%              Number of atoms          :   94 ( 177 expanded)
%              Number of equality atoms :   38 (  78 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_1 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_65,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
      <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_22,plain,(
    ! [A_16] : r1_xboole_0(A_16,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_761,plain,(
    ! [B_130,A_131] :
      ( r1_xboole_0(B_130,A_131)
      | ~ r1_xboole_0(A_131,B_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_764,plain,(
    ! [A_16] : r1_xboole_0(k1_xboole_0,A_16) ),
    inference(resolution,[status(thm)],[c_22,c_761])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_969,plain,(
    ! [A_161,B_162,C_163] :
      ( ~ r1_xboole_0(A_161,B_162)
      | ~ r2_hidden(C_163,k3_xboole_0(A_161,B_162)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_980,plain,(
    ! [A_166,B_167] :
      ( ~ r1_xboole_0(A_166,B_167)
      | k3_xboole_0(A_166,B_167) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_969])).

tff(c_1005,plain,(
    ! [A_168] : k3_xboole_0(k1_xboole_0,A_168) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_764,c_980])).

tff(c_6,plain,(
    ! [A_3,B_4,C_7] :
      ( ~ r1_xboole_0(A_3,B_4)
      | ~ r2_hidden(C_7,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1014,plain,(
    ! [A_168,C_7] :
      ( ~ r1_xboole_0(k1_xboole_0,A_168)
      | ~ r2_hidden(C_7,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1005,c_6])).

tff(c_1022,plain,(
    ! [C_7] : ~ r2_hidden(C_7,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_764,c_1014])).

tff(c_14,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_849,plain,(
    ! [A_148,B_149] :
      ( k4_xboole_0(A_148,B_149) = k1_xboole_0
      | ~ r1_tarski(A_148,B_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_857,plain,(
    ! [B_11] : k4_xboole_0(B_11,B_11) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_849])).

tff(c_73,plain,(
    ! [B_42,A_43] :
      ( r1_xboole_0(B_42,A_43)
      | ~ r1_xboole_0(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_76,plain,(
    ! [A_16] : r1_xboole_0(k1_xboole_0,A_16) ),
    inference(resolution,[status(thm)],[c_22,c_73])).

tff(c_691,plain,(
    ! [A_122,B_123,C_124] :
      ( ~ r1_xboole_0(A_122,B_123)
      | ~ r2_hidden(C_124,k3_xboole_0(A_122,B_123)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_697,plain,(
    ! [A_125,B_126] :
      ( ~ r1_xboole_0(A_125,B_126)
      | k3_xboole_0(A_125,B_126) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_691])).

tff(c_722,plain,(
    ! [A_127] : k3_xboole_0(k1_xboole_0,A_127) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_76,c_697])).

tff(c_727,plain,(
    ! [A_127,C_7] :
      ( ~ r1_xboole_0(k1_xboole_0,A_127)
      | ~ r2_hidden(C_7,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_722,c_6])).

tff(c_735,plain,(
    ! [C_7] : ~ r2_hidden(C_7,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_727])).

tff(c_522,plain,(
    ! [A_103,B_104] :
      ( k4_xboole_0(A_103,B_104) = k1_xboole_0
      | ~ r1_tarski(A_103,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_530,plain,(
    ! [B_11] : k4_xboole_0(B_11,B_11) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_522])).

tff(c_54,plain,
    ( '#skF_5' != '#skF_6'
    | '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_62,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_99,plain,(
    ! [A_50,B_51] :
      ( r1_xboole_0(k1_tarski(A_50),B_51)
      | r2_hidden(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_190,plain,(
    ! [B_63,A_64] :
      ( r1_xboole_0(B_63,k1_tarski(A_64))
      | r2_hidden(A_64,B_63) ) ),
    inference(resolution,[status(thm)],[c_99,c_2])).

tff(c_24,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = A_17
      | ~ r1_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_444,plain,(
    ! [B_95,A_96] :
      ( k4_xboole_0(B_95,k1_tarski(A_96)) = B_95
      | r2_hidden(A_96,B_95) ) ),
    inference(resolution,[status(thm)],[c_190,c_24])).

tff(c_52,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5')
    | '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_83,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_482,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_444,c_83])).

tff(c_28,plain,(
    ! [C_23,A_19] :
      ( C_23 = A_19
      | ~ r2_hidden(C_23,k1_tarski(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_494,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_482,c_28])).

tff(c_498,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_494])).

tff(c_499,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_500,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_56,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) != k1_tarski('#skF_5')
    | k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_631,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_530,c_499,c_499,c_500,c_56])).

tff(c_30,plain,(
    ! [C_23] : r2_hidden(C_23,k1_tarski(C_23)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_644,plain,(
    r2_hidden('#skF_8',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_631,c_30])).

tff(c_739,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_735,c_644])).

tff(c_740,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_741,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_58,plain,
    ( '#skF_5' != '#skF_6'
    | k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_784,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_740,c_740,c_741,c_58])).

tff(c_858,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_857,c_784])).

tff(c_893,plain,(
    r2_hidden('#skF_8',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_858,c_30])).

tff(c_1026,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1022,c_893])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:46:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.39  
% 2.72/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.39  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_1 > #skF_4
% 2.72/1.39  
% 2.72/1.39  %Foreground sorts:
% 2.72/1.39  
% 2.72/1.39  
% 2.72/1.39  %Background operators:
% 2.72/1.39  
% 2.72/1.39  
% 2.72/1.39  %Foreground operators:
% 2.72/1.39  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.72/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.72/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.72/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.72/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.72/1.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.72/1.39  tff('#skF_7', type, '#skF_7': $i).
% 2.72/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.72/1.39  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.72/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.72/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.72/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.72/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.72/1.39  tff('#skF_6', type, '#skF_6': $i).
% 2.72/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.72/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.72/1.39  tff('#skF_8', type, '#skF_8': $i).
% 2.72/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.72/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.72/1.39  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.72/1.39  
% 2.72/1.41  tff(f_65, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.72/1.41  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.72/1.41  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.72/1.41  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.72/1.41  tff(f_57, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.72/1.41  tff(f_61, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.72/1.41  tff(f_99, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.72/1.41  tff(f_89, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.72/1.41  tff(f_69, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.72/1.41  tff(f_76, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.72/1.41  tff(c_22, plain, (![A_16]: (r1_xboole_0(A_16, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.72/1.41  tff(c_761, plain, (![B_130, A_131]: (r1_xboole_0(B_130, A_131) | ~r1_xboole_0(A_131, B_130))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.72/1.41  tff(c_764, plain, (![A_16]: (r1_xboole_0(k1_xboole_0, A_16))), inference(resolution, [status(thm)], [c_22, c_761])).
% 2.72/1.41  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.72/1.41  tff(c_969, plain, (![A_161, B_162, C_163]: (~r1_xboole_0(A_161, B_162) | ~r2_hidden(C_163, k3_xboole_0(A_161, B_162)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.72/1.41  tff(c_980, plain, (![A_166, B_167]: (~r1_xboole_0(A_166, B_167) | k3_xboole_0(A_166, B_167)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_969])).
% 2.72/1.41  tff(c_1005, plain, (![A_168]: (k3_xboole_0(k1_xboole_0, A_168)=k1_xboole_0)), inference(resolution, [status(thm)], [c_764, c_980])).
% 2.72/1.41  tff(c_6, plain, (![A_3, B_4, C_7]: (~r1_xboole_0(A_3, B_4) | ~r2_hidden(C_7, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.72/1.41  tff(c_1014, plain, (![A_168, C_7]: (~r1_xboole_0(k1_xboole_0, A_168) | ~r2_hidden(C_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1005, c_6])).
% 2.72/1.41  tff(c_1022, plain, (![C_7]: (~r2_hidden(C_7, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_764, c_1014])).
% 2.72/1.41  tff(c_14, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.72/1.41  tff(c_849, plain, (![A_148, B_149]: (k4_xboole_0(A_148, B_149)=k1_xboole_0 | ~r1_tarski(A_148, B_149))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.72/1.41  tff(c_857, plain, (![B_11]: (k4_xboole_0(B_11, B_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_849])).
% 2.72/1.41  tff(c_73, plain, (![B_42, A_43]: (r1_xboole_0(B_42, A_43) | ~r1_xboole_0(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.72/1.41  tff(c_76, plain, (![A_16]: (r1_xboole_0(k1_xboole_0, A_16))), inference(resolution, [status(thm)], [c_22, c_73])).
% 2.72/1.41  tff(c_691, plain, (![A_122, B_123, C_124]: (~r1_xboole_0(A_122, B_123) | ~r2_hidden(C_124, k3_xboole_0(A_122, B_123)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.72/1.41  tff(c_697, plain, (![A_125, B_126]: (~r1_xboole_0(A_125, B_126) | k3_xboole_0(A_125, B_126)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_691])).
% 2.72/1.41  tff(c_722, plain, (![A_127]: (k3_xboole_0(k1_xboole_0, A_127)=k1_xboole_0)), inference(resolution, [status(thm)], [c_76, c_697])).
% 2.72/1.41  tff(c_727, plain, (![A_127, C_7]: (~r1_xboole_0(k1_xboole_0, A_127) | ~r2_hidden(C_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_722, c_6])).
% 2.72/1.41  tff(c_735, plain, (![C_7]: (~r2_hidden(C_7, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_727])).
% 2.72/1.41  tff(c_522, plain, (![A_103, B_104]: (k4_xboole_0(A_103, B_104)=k1_xboole_0 | ~r1_tarski(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.72/1.41  tff(c_530, plain, (![B_11]: (k4_xboole_0(B_11, B_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_522])).
% 2.72/1.41  tff(c_54, plain, ('#skF_5'!='#skF_6' | '#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.72/1.41  tff(c_62, plain, ('#skF_5'!='#skF_6'), inference(splitLeft, [status(thm)], [c_54])).
% 2.72/1.41  tff(c_99, plain, (![A_50, B_51]: (r1_xboole_0(k1_tarski(A_50), B_51) | r2_hidden(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.72/1.41  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.72/1.41  tff(c_190, plain, (![B_63, A_64]: (r1_xboole_0(B_63, k1_tarski(A_64)) | r2_hidden(A_64, B_63))), inference(resolution, [status(thm)], [c_99, c_2])).
% 2.72/1.41  tff(c_24, plain, (![A_17, B_18]: (k4_xboole_0(A_17, B_18)=A_17 | ~r1_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.72/1.41  tff(c_444, plain, (![B_95, A_96]: (k4_xboole_0(B_95, k1_tarski(A_96))=B_95 | r2_hidden(A_96, B_95))), inference(resolution, [status(thm)], [c_190, c_24])).
% 2.72/1.41  tff(c_52, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5') | '#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.72/1.41  tff(c_83, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5')), inference(splitLeft, [status(thm)], [c_52])).
% 2.72/1.41  tff(c_482, plain, (r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_444, c_83])).
% 2.72/1.41  tff(c_28, plain, (![C_23, A_19]: (C_23=A_19 | ~r2_hidden(C_23, k1_tarski(A_19)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.72/1.41  tff(c_494, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_482, c_28])).
% 2.72/1.41  tff(c_498, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_494])).
% 2.72/1.41  tff(c_499, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_52])).
% 2.72/1.41  tff(c_500, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_52])).
% 2.72/1.41  tff(c_56, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))!=k1_tarski('#skF_5') | k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.72/1.41  tff(c_631, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_530, c_499, c_499, c_500, c_56])).
% 2.72/1.41  tff(c_30, plain, (![C_23]: (r2_hidden(C_23, k1_tarski(C_23)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.72/1.41  tff(c_644, plain, (r2_hidden('#skF_8', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_631, c_30])).
% 2.72/1.41  tff(c_739, plain, $false, inference(negUnitSimplification, [status(thm)], [c_735, c_644])).
% 2.72/1.41  tff(c_740, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_54])).
% 2.72/1.41  tff(c_741, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_54])).
% 2.72/1.41  tff(c_58, plain, ('#skF_5'!='#skF_6' | k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.72/1.41  tff(c_784, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_740, c_740, c_741, c_58])).
% 2.72/1.41  tff(c_858, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_857, c_784])).
% 2.72/1.41  tff(c_893, plain, (r2_hidden('#skF_8', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_858, c_30])).
% 2.72/1.41  tff(c_1026, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1022, c_893])).
% 2.72/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.41  
% 2.72/1.41  Inference rules
% 2.72/1.41  ----------------------
% 2.72/1.41  #Ref     : 0
% 2.72/1.41  #Sup     : 218
% 2.72/1.41  #Fact    : 0
% 2.72/1.41  #Define  : 0
% 2.72/1.41  #Split   : 3
% 2.72/1.41  #Chain   : 0
% 2.72/1.41  #Close   : 0
% 2.72/1.41  
% 2.72/1.41  Ordering : KBO
% 2.72/1.41  
% 2.72/1.41  Simplification rules
% 2.72/1.41  ----------------------
% 2.72/1.41  #Subsume      : 15
% 2.72/1.41  #Demod        : 57
% 2.72/1.41  #Tautology    : 139
% 2.72/1.41  #SimpNegUnit  : 10
% 2.72/1.41  #BackRed      : 4
% 2.72/1.41  
% 2.72/1.41  #Partial instantiations: 0
% 2.72/1.41  #Strategies tried      : 1
% 2.72/1.41  
% 2.72/1.41  Timing (in seconds)
% 2.72/1.41  ----------------------
% 2.72/1.41  Preprocessing        : 0.32
% 2.72/1.41  Parsing              : 0.17
% 2.72/1.41  CNF conversion       : 0.02
% 2.72/1.41  Main loop            : 0.32
% 2.72/1.41  Inferencing          : 0.13
% 2.72/1.41  Reduction            : 0.09
% 2.72/1.41  Demodulation         : 0.06
% 2.72/1.41  BG Simplification    : 0.02
% 2.72/1.41  Subsumption          : 0.05
% 2.72/1.41  Abstraction          : 0.02
% 2.72/1.41  MUC search           : 0.00
% 2.72/1.41  Cooper               : 0.00
% 2.72/1.41  Total                : 0.67
% 2.72/1.41  Index Insertion      : 0.00
% 2.72/1.41  Index Deletion       : 0.00
% 2.72/1.41  Index Matching       : 0.00
% 2.72/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
