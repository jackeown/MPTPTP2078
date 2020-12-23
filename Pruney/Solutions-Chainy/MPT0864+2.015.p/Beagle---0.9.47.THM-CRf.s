%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:10 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 129 expanded)
%              Number of leaves         :   30 (  59 expanded)
%              Depth                    :    8
%              Number of atoms          :  102 ( 232 expanded)
%              Number of equality atoms :   60 ( 138 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_1 > #skF_10 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_61,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_83,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_613,plain,(
    ! [A_124,B_125] : k1_enumset1(A_124,A_124,B_125) = k2_tarski(A_124,B_125) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    ! [E_13,A_7,B_8] : r2_hidden(E_13,k1_enumset1(A_7,B_8,E_13)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_625,plain,(
    ! [B_125,A_124] : r2_hidden(B_125,k2_tarski(A_124,B_125)) ),
    inference(superposition,[status(thm),theory(equality)],[c_613,c_22])).

tff(c_66,plain,(
    ! [A_27] :
      ( r2_hidden('#skF_7'(A_27),A_27)
      | k1_xboole_0 = A_27 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_637,plain,(
    ! [D_128,A_129,B_130] :
      ( r2_hidden(D_128,A_129)
      | ~ r2_hidden(D_128,k4_xboole_0(A_129,B_130)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_642,plain,(
    ! [A_129,B_130] :
      ( r2_hidden('#skF_7'(k4_xboole_0(A_129,B_130)),A_129)
      | k4_xboole_0(A_129,B_130) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_66,c_637])).

tff(c_662,plain,(
    ! [D_134,B_135,A_136] :
      ( ~ r2_hidden(D_134,B_135)
      | ~ r2_hidden(D_134,k4_xboole_0(A_136,B_135)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_760,plain,(
    ! [A_158,B_159] :
      ( ~ r2_hidden('#skF_7'(k4_xboole_0(A_158,B_159)),B_159)
      | k4_xboole_0(A_158,B_159) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_66,c_662])).

tff(c_786,plain,(
    ! [A_163] : k4_xboole_0(A_163,A_163) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_642,c_760])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_810,plain,(
    ! [D_164,A_165] :
      ( ~ r2_hidden(D_164,A_165)
      | ~ r2_hidden(D_164,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_786,c_4])).

tff(c_831,plain,(
    ! [B_125] : ~ r2_hidden(B_125,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_625,c_810])).

tff(c_160,plain,(
    ! [A_57,B_58] : k1_enumset1(A_57,A_57,B_58) = k2_tarski(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_172,plain,(
    ! [B_58,A_57] : r2_hidden(B_58,k2_tarski(A_57,B_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_22])).

tff(c_209,plain,(
    ! [D_67,A_68,B_69] :
      ( r2_hidden(D_67,A_68)
      | ~ r2_hidden(D_67,k4_xboole_0(A_68,B_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_286,plain,(
    ! [A_91,B_92] :
      ( r2_hidden('#skF_7'(k4_xboole_0(A_91,B_92)),A_91)
      | k4_xboole_0(A_91,B_92) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_66,c_209])).

tff(c_184,plain,(
    ! [D_61,B_62,A_63] :
      ( ~ r2_hidden(D_61,B_62)
      | ~ r2_hidden(D_61,k4_xboole_0(A_63,B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_189,plain,(
    ! [A_63,B_62] :
      ( ~ r2_hidden('#skF_7'(k4_xboole_0(A_63,B_62)),B_62)
      | k4_xboole_0(A_63,B_62) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_66,c_184])).

tff(c_313,plain,(
    ! [A_93] : k4_xboole_0(A_93,A_93) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_286,c_189])).

tff(c_367,plain,(
    ! [D_99,A_100] :
      ( ~ r2_hidden(D_99,A_100)
      | ~ r2_hidden(D_99,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_4])).

tff(c_388,plain,(
    ! [B_58] : ~ r2_hidden(B_58,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_172,c_367])).

tff(c_74,plain,(
    k4_tarski('#skF_9','#skF_10') = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_105,plain,(
    ! [A_43,B_44] : k1_mcart_1(k4_tarski(A_43,B_44)) = A_43 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_114,plain,(
    k1_mcart_1('#skF_8') = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_105])).

tff(c_89,plain,(
    ! [A_41,B_42] : k2_mcart_1(k4_tarski(A_41,B_42)) = B_42 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_98,plain,(
    k2_mcart_1('#skF_8') = '#skF_10' ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_89])).

tff(c_72,plain,
    ( k2_mcart_1('#skF_8') = '#skF_8'
    | k1_mcart_1('#skF_8') = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_128,plain,
    ( '#skF_10' = '#skF_8'
    | '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_98,c_72])).

tff(c_129,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_131,plain,(
    k4_tarski('#skF_8','#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_74])).

tff(c_153,plain,(
    ! [A_53] :
      ( r2_hidden('#skF_7'(A_53),A_53)
      | k1_xboole_0 = A_53 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_44,plain,(
    ! [C_18,A_14] :
      ( C_18 = A_14
      | ~ r2_hidden(C_18,k1_tarski(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_158,plain,(
    ! [A_14] :
      ( '#skF_7'(k1_tarski(A_14)) = A_14
      | k1_tarski(A_14) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_153,c_44])).

tff(c_46,plain,(
    ! [C_18] : r2_hidden(C_18,k1_tarski(C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_246,plain,(
    ! [C_76,A_77,D_78] :
      ( ~ r2_hidden(C_76,A_77)
      | k4_tarski(C_76,D_78) != '#skF_7'(A_77)
      | k1_xboole_0 = A_77 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_276,plain,(
    ! [C_83,D_84] :
      ( k4_tarski(C_83,D_84) != '#skF_7'(k1_tarski(C_83))
      | k1_tarski(C_83) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_46,c_246])).

tff(c_553,plain,(
    ! [A_115,D_116] :
      ( k4_tarski(A_115,D_116) != A_115
      | k1_tarski(A_115) = k1_xboole_0
      | k1_tarski(A_115) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_276])).

tff(c_557,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_553])).

tff(c_573,plain,(
    r2_hidden('#skF_8',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_557,c_46])).

tff(c_580,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_388,c_573])).

tff(c_581,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_585,plain,(
    k4_tarski('#skF_9','#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_581,c_74])).

tff(c_607,plain,(
    ! [A_123] :
      ( r2_hidden('#skF_7'(A_123),A_123)
      | k1_xboole_0 = A_123 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_612,plain,(
    ! [A_14] :
      ( '#skF_7'(k1_tarski(A_14)) = A_14
      | k1_tarski(A_14) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_607,c_44])).

tff(c_677,plain,(
    ! [D_140,A_141,C_142] :
      ( ~ r2_hidden(D_140,A_141)
      | k4_tarski(C_142,D_140) != '#skF_7'(A_141)
      | k1_xboole_0 = A_141 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_703,plain,(
    ! [C_145,C_146] :
      ( k4_tarski(C_145,C_146) != '#skF_7'(k1_tarski(C_146))
      | k1_tarski(C_146) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_46,c_677])).

tff(c_995,plain,(
    ! [C_180,A_181] :
      ( k4_tarski(C_180,A_181) != A_181
      | k1_tarski(A_181) = k1_xboole_0
      | k1_tarski(A_181) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_612,c_703])).

tff(c_999,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_585,c_995])).

tff(c_1015,plain,(
    r2_hidden('#skF_8',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_999,c_46])).

tff(c_1022,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_831,c_1015])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:15:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.54  
% 3.02/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.54  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_1 > #skF_10 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_5
% 3.02/1.54  
% 3.02/1.54  %Foreground sorts:
% 3.02/1.54  
% 3.02/1.54  
% 3.02/1.54  %Background operators:
% 3.02/1.54  
% 3.02/1.54  
% 3.02/1.54  %Foreground operators:
% 3.02/1.54  tff('#skF_7', type, '#skF_7': $i > $i).
% 3.02/1.54  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.02/1.54  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.02/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.02/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.02/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.02/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.02/1.54  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.02/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.02/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.02/1.54  tff('#skF_10', type, '#skF_10': $i).
% 3.02/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.02/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.02/1.54  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.02/1.54  tff('#skF_9', type, '#skF_9': $i).
% 3.02/1.54  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.02/1.54  tff('#skF_8', type, '#skF_8': $i).
% 3.02/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.02/1.54  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.02/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.02/1.54  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.02/1.54  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.02/1.54  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.02/1.54  
% 3.02/1.55  tff(f_61, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.02/1.55  tff(f_50, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.02/1.55  tff(f_83, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 3.02/1.55  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.02/1.55  tff(f_93, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 3.02/1.55  tff(f_67, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.02/1.55  tff(f_57, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.02/1.55  tff(c_613, plain, (![A_124, B_125]: (k1_enumset1(A_124, A_124, B_125)=k2_tarski(A_124, B_125))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.02/1.55  tff(c_22, plain, (![E_13, A_7, B_8]: (r2_hidden(E_13, k1_enumset1(A_7, B_8, E_13)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.02/1.55  tff(c_625, plain, (![B_125, A_124]: (r2_hidden(B_125, k2_tarski(A_124, B_125)))), inference(superposition, [status(thm), theory('equality')], [c_613, c_22])).
% 3.02/1.55  tff(c_66, plain, (![A_27]: (r2_hidden('#skF_7'(A_27), A_27) | k1_xboole_0=A_27)), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.02/1.55  tff(c_637, plain, (![D_128, A_129, B_130]: (r2_hidden(D_128, A_129) | ~r2_hidden(D_128, k4_xboole_0(A_129, B_130)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.02/1.55  tff(c_642, plain, (![A_129, B_130]: (r2_hidden('#skF_7'(k4_xboole_0(A_129, B_130)), A_129) | k4_xboole_0(A_129, B_130)=k1_xboole_0)), inference(resolution, [status(thm)], [c_66, c_637])).
% 3.02/1.55  tff(c_662, plain, (![D_134, B_135, A_136]: (~r2_hidden(D_134, B_135) | ~r2_hidden(D_134, k4_xboole_0(A_136, B_135)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.02/1.55  tff(c_760, plain, (![A_158, B_159]: (~r2_hidden('#skF_7'(k4_xboole_0(A_158, B_159)), B_159) | k4_xboole_0(A_158, B_159)=k1_xboole_0)), inference(resolution, [status(thm)], [c_66, c_662])).
% 3.02/1.55  tff(c_786, plain, (![A_163]: (k4_xboole_0(A_163, A_163)=k1_xboole_0)), inference(resolution, [status(thm)], [c_642, c_760])).
% 3.02/1.55  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.02/1.55  tff(c_810, plain, (![D_164, A_165]: (~r2_hidden(D_164, A_165) | ~r2_hidden(D_164, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_786, c_4])).
% 3.02/1.55  tff(c_831, plain, (![B_125]: (~r2_hidden(B_125, k1_xboole_0))), inference(resolution, [status(thm)], [c_625, c_810])).
% 3.02/1.55  tff(c_160, plain, (![A_57, B_58]: (k1_enumset1(A_57, A_57, B_58)=k2_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.02/1.55  tff(c_172, plain, (![B_58, A_57]: (r2_hidden(B_58, k2_tarski(A_57, B_58)))), inference(superposition, [status(thm), theory('equality')], [c_160, c_22])).
% 3.02/1.55  tff(c_209, plain, (![D_67, A_68, B_69]: (r2_hidden(D_67, A_68) | ~r2_hidden(D_67, k4_xboole_0(A_68, B_69)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.02/1.55  tff(c_286, plain, (![A_91, B_92]: (r2_hidden('#skF_7'(k4_xboole_0(A_91, B_92)), A_91) | k4_xboole_0(A_91, B_92)=k1_xboole_0)), inference(resolution, [status(thm)], [c_66, c_209])).
% 3.02/1.55  tff(c_184, plain, (![D_61, B_62, A_63]: (~r2_hidden(D_61, B_62) | ~r2_hidden(D_61, k4_xboole_0(A_63, B_62)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.02/1.55  tff(c_189, plain, (![A_63, B_62]: (~r2_hidden('#skF_7'(k4_xboole_0(A_63, B_62)), B_62) | k4_xboole_0(A_63, B_62)=k1_xboole_0)), inference(resolution, [status(thm)], [c_66, c_184])).
% 3.02/1.55  tff(c_313, plain, (![A_93]: (k4_xboole_0(A_93, A_93)=k1_xboole_0)), inference(resolution, [status(thm)], [c_286, c_189])).
% 3.02/1.55  tff(c_367, plain, (![D_99, A_100]: (~r2_hidden(D_99, A_100) | ~r2_hidden(D_99, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_313, c_4])).
% 3.02/1.55  tff(c_388, plain, (![B_58]: (~r2_hidden(B_58, k1_xboole_0))), inference(resolution, [status(thm)], [c_172, c_367])).
% 3.02/1.55  tff(c_74, plain, (k4_tarski('#skF_9', '#skF_10')='#skF_8'), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.02/1.55  tff(c_105, plain, (![A_43, B_44]: (k1_mcart_1(k4_tarski(A_43, B_44))=A_43)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.02/1.55  tff(c_114, plain, (k1_mcart_1('#skF_8')='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_74, c_105])).
% 3.02/1.55  tff(c_89, plain, (![A_41, B_42]: (k2_mcart_1(k4_tarski(A_41, B_42))=B_42)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.02/1.55  tff(c_98, plain, (k2_mcart_1('#skF_8')='#skF_10'), inference(superposition, [status(thm), theory('equality')], [c_74, c_89])).
% 3.02/1.55  tff(c_72, plain, (k2_mcart_1('#skF_8')='#skF_8' | k1_mcart_1('#skF_8')='#skF_8'), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.02/1.55  tff(c_128, plain, ('#skF_10'='#skF_8' | '#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_114, c_98, c_72])).
% 3.02/1.55  tff(c_129, plain, ('#skF_9'='#skF_8'), inference(splitLeft, [status(thm)], [c_128])).
% 3.02/1.55  tff(c_131, plain, (k4_tarski('#skF_8', '#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_129, c_74])).
% 3.02/1.55  tff(c_153, plain, (![A_53]: (r2_hidden('#skF_7'(A_53), A_53) | k1_xboole_0=A_53)), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.02/1.55  tff(c_44, plain, (![C_18, A_14]: (C_18=A_14 | ~r2_hidden(C_18, k1_tarski(A_14)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.02/1.55  tff(c_158, plain, (![A_14]: ('#skF_7'(k1_tarski(A_14))=A_14 | k1_tarski(A_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_153, c_44])).
% 3.02/1.55  tff(c_46, plain, (![C_18]: (r2_hidden(C_18, k1_tarski(C_18)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.02/1.55  tff(c_246, plain, (![C_76, A_77, D_78]: (~r2_hidden(C_76, A_77) | k4_tarski(C_76, D_78)!='#skF_7'(A_77) | k1_xboole_0=A_77)), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.02/1.55  tff(c_276, plain, (![C_83, D_84]: (k4_tarski(C_83, D_84)!='#skF_7'(k1_tarski(C_83)) | k1_tarski(C_83)=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_246])).
% 3.02/1.55  tff(c_553, plain, (![A_115, D_116]: (k4_tarski(A_115, D_116)!=A_115 | k1_tarski(A_115)=k1_xboole_0 | k1_tarski(A_115)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_158, c_276])).
% 3.02/1.55  tff(c_557, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_131, c_553])).
% 3.02/1.55  tff(c_573, plain, (r2_hidden('#skF_8', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_557, c_46])).
% 3.02/1.55  tff(c_580, plain, $false, inference(negUnitSimplification, [status(thm)], [c_388, c_573])).
% 3.02/1.55  tff(c_581, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_128])).
% 3.02/1.55  tff(c_585, plain, (k4_tarski('#skF_9', '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_581, c_74])).
% 3.02/1.55  tff(c_607, plain, (![A_123]: (r2_hidden('#skF_7'(A_123), A_123) | k1_xboole_0=A_123)), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.02/1.55  tff(c_612, plain, (![A_14]: ('#skF_7'(k1_tarski(A_14))=A_14 | k1_tarski(A_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_607, c_44])).
% 3.02/1.55  tff(c_677, plain, (![D_140, A_141, C_142]: (~r2_hidden(D_140, A_141) | k4_tarski(C_142, D_140)!='#skF_7'(A_141) | k1_xboole_0=A_141)), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.02/1.55  tff(c_703, plain, (![C_145, C_146]: (k4_tarski(C_145, C_146)!='#skF_7'(k1_tarski(C_146)) | k1_tarski(C_146)=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_677])).
% 3.02/1.55  tff(c_995, plain, (![C_180, A_181]: (k4_tarski(C_180, A_181)!=A_181 | k1_tarski(A_181)=k1_xboole_0 | k1_tarski(A_181)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_612, c_703])).
% 3.02/1.55  tff(c_999, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_585, c_995])).
% 3.02/1.55  tff(c_1015, plain, (r2_hidden('#skF_8', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_999, c_46])).
% 3.02/1.55  tff(c_1022, plain, $false, inference(negUnitSimplification, [status(thm)], [c_831, c_1015])).
% 3.02/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.55  
% 3.02/1.55  Inference rules
% 3.02/1.55  ----------------------
% 3.02/1.55  #Ref     : 0
% 3.02/1.55  #Sup     : 241
% 3.02/1.55  #Fact    : 0
% 3.02/1.55  #Define  : 0
% 3.02/1.55  #Split   : 2
% 3.02/1.55  #Chain   : 0
% 3.02/1.55  #Close   : 0
% 3.02/1.55  
% 3.02/1.55  Ordering : KBO
% 3.02/1.55  
% 3.02/1.55  Simplification rules
% 3.02/1.55  ----------------------
% 3.02/1.55  #Subsume      : 37
% 3.02/1.55  #Demod        : 34
% 3.02/1.55  #Tautology    : 102
% 3.02/1.56  #SimpNegUnit  : 10
% 3.02/1.56  #BackRed      : 4
% 3.02/1.56  
% 3.02/1.56  #Partial instantiations: 0
% 3.02/1.56  #Strategies tried      : 1
% 3.02/1.56  
% 3.02/1.56  Timing (in seconds)
% 3.02/1.56  ----------------------
% 3.02/1.56  Preprocessing        : 0.34
% 3.02/1.56  Parsing              : 0.17
% 3.02/1.56  CNF conversion       : 0.03
% 3.02/1.56  Main loop            : 0.37
% 3.02/1.56  Inferencing          : 0.13
% 3.02/1.56  Reduction            : 0.11
% 3.02/1.56  Demodulation         : 0.08
% 3.02/1.56  BG Simplification    : 0.03
% 3.02/1.56  Subsumption          : 0.07
% 3.02/1.56  Abstraction          : 0.03
% 3.02/1.56  MUC search           : 0.00
% 3.02/1.56  Cooper               : 0.00
% 3.02/1.56  Total                : 0.75
% 3.02/1.56  Index Insertion      : 0.00
% 3.02/1.56  Index Deletion       : 0.00
% 3.02/1.56  Index Matching       : 0.00
% 3.02/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
