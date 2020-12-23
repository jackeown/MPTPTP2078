%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:14 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 122 expanded)
%              Number of leaves         :   25 (  54 expanded)
%              Depth                    :    8
%              Number of atoms          :   99 ( 238 expanded)
%              Number of equality atoms :   61 ( 146 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_68,axiom,(
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

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_22,plain,(
    ! [D_12,A_7] : r2_hidden(D_12,k2_tarski(A_7,D_12)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_46,plain,(
    ! [A_20] :
      ( r2_hidden('#skF_5'(A_20),A_20)
      | k1_xboole_0 = A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_761,plain,(
    ! [D_130,A_131,B_132] :
      ( r2_hidden(D_130,A_131)
      | ~ r2_hidden(D_130,k4_xboole_0(A_131,B_132)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_815,plain,(
    ! [A_151,B_152] :
      ( r2_hidden('#skF_5'(k4_xboole_0(A_151,B_152)),A_151)
      | k4_xboole_0(A_151,B_152) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_46,c_761])).

tff(c_755,plain,(
    ! [D_127,B_128,A_129] :
      ( ~ r2_hidden(D_127,B_128)
      | ~ r2_hidden(D_127,k4_xboole_0(A_129,B_128)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_760,plain,(
    ! [A_129,B_128] :
      ( ~ r2_hidden('#skF_5'(k4_xboole_0(A_129,B_128)),B_128)
      | k4_xboole_0(A_129,B_128) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_46,c_755])).

tff(c_862,plain,(
    ! [A_156] : k4_xboole_0(A_156,A_156) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_815,c_760])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_896,plain,(
    ! [D_159,A_160] :
      ( ~ r2_hidden(D_159,A_160)
      | ~ r2_hidden(D_159,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_862,c_4])).

tff(c_910,plain,(
    ! [D_12] : ~ r2_hidden(D_12,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_896])).

tff(c_127,plain,(
    ! [D_43,A_44,B_45] :
      ( r2_hidden(D_43,A_44)
      | ~ r2_hidden(D_43,k4_xboole_0(A_44,B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_187,plain,(
    ! [A_67,B_68] :
      ( r2_hidden('#skF_5'(k4_xboole_0(A_67,B_68)),A_67)
      | k4_xboole_0(A_67,B_68) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_46,c_127])).

tff(c_133,plain,(
    ! [D_46,B_47,A_48] :
      ( ~ r2_hidden(D_46,B_47)
      | ~ r2_hidden(D_46,k4_xboole_0(A_48,B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_138,plain,(
    ! [A_48,B_47] :
      ( ~ r2_hidden('#skF_5'(k4_xboole_0(A_48,B_47)),B_47)
      | k4_xboole_0(A_48,B_47) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_46,c_133])).

tff(c_214,plain,(
    ! [A_69] : k4_xboole_0(A_69,A_69) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_187,c_138])).

tff(c_235,plain,(
    ! [D_70,A_71] :
      ( ~ r2_hidden(D_70,A_71)
      | ~ r2_hidden(D_70,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_4])).

tff(c_246,plain,(
    ! [D_12] : ~ r2_hidden(D_12,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_235])).

tff(c_54,plain,(
    k4_tarski('#skF_7','#skF_8') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_77,plain,(
    ! [A_38,B_39] : k1_mcart_1(k4_tarski(A_38,B_39)) = A_38 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_86,plain,(
    k1_mcart_1('#skF_6') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_77])).

tff(c_61,plain,(
    ! [A_36,B_37] : k2_mcart_1(k4_tarski(A_36,B_37)) = B_37 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_70,plain,(
    k2_mcart_1('#skF_6') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_61])).

tff(c_52,plain,
    ( k2_mcart_1('#skF_6') = '#skF_6'
    | k1_mcart_1('#skF_6') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_94,plain,
    ( '#skF_6' = '#skF_8'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_70,c_52])).

tff(c_95,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_97,plain,(
    k4_tarski('#skF_6','#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_54])).

tff(c_148,plain,(
    ! [D_52,B_53,A_54] :
      ( D_52 = B_53
      | D_52 = A_54
      | ~ r2_hidden(D_52,k2_tarski(A_54,B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_159,plain,(
    ! [A_54,B_53] :
      ( '#skF_5'(k2_tarski(A_54,B_53)) = B_53
      | '#skF_5'(k2_tarski(A_54,B_53)) = A_54
      | k2_tarski(A_54,B_53) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_46,c_148])).

tff(c_602,plain,(
    ! [B_119] :
      ( k2_tarski(B_119,B_119) = k1_xboole_0
      | '#skF_5'(k2_tarski(B_119,B_119)) = B_119 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_159])).

tff(c_24,plain,(
    ! [D_12,B_8] : r2_hidden(D_12,k2_tarski(D_12,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_164,plain,(
    ! [C_55,A_56,D_57] :
      ( ~ r2_hidden(C_55,A_56)
      | k4_tarski(C_55,D_57) != '#skF_5'(A_56)
      | k1_xboole_0 = A_56 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_173,plain,(
    ! [D_12,D_57,B_8] :
      ( k4_tarski(D_12,D_57) != '#skF_5'(k2_tarski(D_12,B_8))
      | k2_tarski(D_12,B_8) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_164])).

tff(c_670,plain,(
    ! [B_123,D_124] :
      ( k4_tarski(B_123,D_124) != B_123
      | k2_tarski(B_123,B_123) = k1_xboole_0
      | k2_tarski(B_123,B_123) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_602,c_173])).

tff(c_673,plain,(
    k2_tarski('#skF_6','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_670])).

tff(c_701,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_673,c_22])).

tff(c_715,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_246,c_701])).

tff(c_716,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_720,plain,(
    k4_tarski('#skF_7','#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_716,c_54])).

tff(c_767,plain,(
    ! [D_133,B_134,A_135] :
      ( D_133 = B_134
      | D_133 = A_135
      | ~ r2_hidden(D_133,k2_tarski(A_135,B_134)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_778,plain,(
    ! [A_135,B_134] :
      ( '#skF_5'(k2_tarski(A_135,B_134)) = B_134
      | '#skF_5'(k2_tarski(A_135,B_134)) = A_135
      | k2_tarski(A_135,B_134) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_46,c_767])).

tff(c_1091,plain,(
    ! [B_186] :
      ( k2_tarski(B_186,B_186) = k1_xboole_0
      | '#skF_5'(k2_tarski(B_186,B_186)) = B_186 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_778])).

tff(c_803,plain,(
    ! [D_144,A_145,C_146] :
      ( ~ r2_hidden(D_144,A_145)
      | k4_tarski(C_146,D_144) != '#skF_5'(A_145)
      | k1_xboole_0 = A_145 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_811,plain,(
    ! [C_146,D_12,A_7] :
      ( k4_tarski(C_146,D_12) != '#skF_5'(k2_tarski(A_7,D_12))
      | k2_tarski(A_7,D_12) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_803])).

tff(c_1141,plain,(
    ! [C_192,B_193] :
      ( k4_tarski(C_192,B_193) != B_193
      | k2_tarski(B_193,B_193) = k1_xboole_0
      | k2_tarski(B_193,B_193) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1091,c_811])).

tff(c_1144,plain,(
    k2_tarski('#skF_8','#skF_8') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_720,c_1141])).

tff(c_1172,plain,(
    r2_hidden('#skF_8',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1144,c_22])).

tff(c_1186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_910,c_1172])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:19:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.61  
% 2.72/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.61  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3
% 2.72/1.61  
% 2.72/1.61  %Foreground sorts:
% 2.72/1.61  
% 2.72/1.61  
% 2.72/1.61  %Background operators:
% 2.72/1.61  
% 2.72/1.61  
% 2.72/1.61  %Foreground operators:
% 2.72/1.61  tff('#skF_5', type, '#skF_5': $i > $i).
% 2.72/1.61  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.72/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.72/1.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.72/1.61  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.72/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.72/1.61  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.72/1.61  tff('#skF_7', type, '#skF_7': $i).
% 2.72/1.61  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.72/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.72/1.61  tff('#skF_6', type, '#skF_6': $i).
% 2.72/1.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.72/1.61  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.72/1.61  tff('#skF_8', type, '#skF_8': $i).
% 2.72/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.61  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.72/1.61  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.72/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.61  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.72/1.61  
% 3.01/1.63  tff(f_44, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 3.01/1.63  tff(f_68, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 3.01/1.63  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.01/1.63  tff(f_78, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 3.01/1.63  tff(f_52, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.01/1.63  tff(c_22, plain, (![D_12, A_7]: (r2_hidden(D_12, k2_tarski(A_7, D_12)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.01/1.63  tff(c_46, plain, (![A_20]: (r2_hidden('#skF_5'(A_20), A_20) | k1_xboole_0=A_20)), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.01/1.63  tff(c_761, plain, (![D_130, A_131, B_132]: (r2_hidden(D_130, A_131) | ~r2_hidden(D_130, k4_xboole_0(A_131, B_132)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.01/1.63  tff(c_815, plain, (![A_151, B_152]: (r2_hidden('#skF_5'(k4_xboole_0(A_151, B_152)), A_151) | k4_xboole_0(A_151, B_152)=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_761])).
% 3.01/1.63  tff(c_755, plain, (![D_127, B_128, A_129]: (~r2_hidden(D_127, B_128) | ~r2_hidden(D_127, k4_xboole_0(A_129, B_128)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.01/1.63  tff(c_760, plain, (![A_129, B_128]: (~r2_hidden('#skF_5'(k4_xboole_0(A_129, B_128)), B_128) | k4_xboole_0(A_129, B_128)=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_755])).
% 3.01/1.63  tff(c_862, plain, (![A_156]: (k4_xboole_0(A_156, A_156)=k1_xboole_0)), inference(resolution, [status(thm)], [c_815, c_760])).
% 3.01/1.63  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.01/1.63  tff(c_896, plain, (![D_159, A_160]: (~r2_hidden(D_159, A_160) | ~r2_hidden(D_159, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_862, c_4])).
% 3.01/1.63  tff(c_910, plain, (![D_12]: (~r2_hidden(D_12, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_896])).
% 3.01/1.63  tff(c_127, plain, (![D_43, A_44, B_45]: (r2_hidden(D_43, A_44) | ~r2_hidden(D_43, k4_xboole_0(A_44, B_45)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.01/1.63  tff(c_187, plain, (![A_67, B_68]: (r2_hidden('#skF_5'(k4_xboole_0(A_67, B_68)), A_67) | k4_xboole_0(A_67, B_68)=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_127])).
% 3.01/1.63  tff(c_133, plain, (![D_46, B_47, A_48]: (~r2_hidden(D_46, B_47) | ~r2_hidden(D_46, k4_xboole_0(A_48, B_47)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.01/1.63  tff(c_138, plain, (![A_48, B_47]: (~r2_hidden('#skF_5'(k4_xboole_0(A_48, B_47)), B_47) | k4_xboole_0(A_48, B_47)=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_133])).
% 3.01/1.63  tff(c_214, plain, (![A_69]: (k4_xboole_0(A_69, A_69)=k1_xboole_0)), inference(resolution, [status(thm)], [c_187, c_138])).
% 3.01/1.63  tff(c_235, plain, (![D_70, A_71]: (~r2_hidden(D_70, A_71) | ~r2_hidden(D_70, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_214, c_4])).
% 3.01/1.63  tff(c_246, plain, (![D_12]: (~r2_hidden(D_12, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_235])).
% 3.01/1.63  tff(c_54, plain, (k4_tarski('#skF_7', '#skF_8')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.01/1.63  tff(c_77, plain, (![A_38, B_39]: (k1_mcart_1(k4_tarski(A_38, B_39))=A_38)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.01/1.63  tff(c_86, plain, (k1_mcart_1('#skF_6')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_54, c_77])).
% 3.01/1.63  tff(c_61, plain, (![A_36, B_37]: (k2_mcart_1(k4_tarski(A_36, B_37))=B_37)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.01/1.63  tff(c_70, plain, (k2_mcart_1('#skF_6')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_54, c_61])).
% 3.01/1.63  tff(c_52, plain, (k2_mcart_1('#skF_6')='#skF_6' | k1_mcart_1('#skF_6')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.01/1.63  tff(c_94, plain, ('#skF_6'='#skF_8' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_70, c_52])).
% 3.01/1.63  tff(c_95, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_94])).
% 3.01/1.63  tff(c_97, plain, (k4_tarski('#skF_6', '#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_95, c_54])).
% 3.01/1.63  tff(c_148, plain, (![D_52, B_53, A_54]: (D_52=B_53 | D_52=A_54 | ~r2_hidden(D_52, k2_tarski(A_54, B_53)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.01/1.63  tff(c_159, plain, (![A_54, B_53]: ('#skF_5'(k2_tarski(A_54, B_53))=B_53 | '#skF_5'(k2_tarski(A_54, B_53))=A_54 | k2_tarski(A_54, B_53)=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_148])).
% 3.01/1.63  tff(c_602, plain, (![B_119]: (k2_tarski(B_119, B_119)=k1_xboole_0 | '#skF_5'(k2_tarski(B_119, B_119))=B_119)), inference(factorization, [status(thm), theory('equality')], [c_159])).
% 3.01/1.63  tff(c_24, plain, (![D_12, B_8]: (r2_hidden(D_12, k2_tarski(D_12, B_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.01/1.63  tff(c_164, plain, (![C_55, A_56, D_57]: (~r2_hidden(C_55, A_56) | k4_tarski(C_55, D_57)!='#skF_5'(A_56) | k1_xboole_0=A_56)), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.01/1.63  tff(c_173, plain, (![D_12, D_57, B_8]: (k4_tarski(D_12, D_57)!='#skF_5'(k2_tarski(D_12, B_8)) | k2_tarski(D_12, B_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_164])).
% 3.01/1.63  tff(c_670, plain, (![B_123, D_124]: (k4_tarski(B_123, D_124)!=B_123 | k2_tarski(B_123, B_123)=k1_xboole_0 | k2_tarski(B_123, B_123)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_602, c_173])).
% 3.01/1.63  tff(c_673, plain, (k2_tarski('#skF_6', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_97, c_670])).
% 3.01/1.63  tff(c_701, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_673, c_22])).
% 3.01/1.63  tff(c_715, plain, $false, inference(negUnitSimplification, [status(thm)], [c_246, c_701])).
% 3.01/1.63  tff(c_716, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_94])).
% 3.01/1.63  tff(c_720, plain, (k4_tarski('#skF_7', '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_716, c_54])).
% 3.01/1.63  tff(c_767, plain, (![D_133, B_134, A_135]: (D_133=B_134 | D_133=A_135 | ~r2_hidden(D_133, k2_tarski(A_135, B_134)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.01/1.63  tff(c_778, plain, (![A_135, B_134]: ('#skF_5'(k2_tarski(A_135, B_134))=B_134 | '#skF_5'(k2_tarski(A_135, B_134))=A_135 | k2_tarski(A_135, B_134)=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_767])).
% 3.01/1.63  tff(c_1091, plain, (![B_186]: (k2_tarski(B_186, B_186)=k1_xboole_0 | '#skF_5'(k2_tarski(B_186, B_186))=B_186)), inference(factorization, [status(thm), theory('equality')], [c_778])).
% 3.01/1.63  tff(c_803, plain, (![D_144, A_145, C_146]: (~r2_hidden(D_144, A_145) | k4_tarski(C_146, D_144)!='#skF_5'(A_145) | k1_xboole_0=A_145)), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.01/1.63  tff(c_811, plain, (![C_146, D_12, A_7]: (k4_tarski(C_146, D_12)!='#skF_5'(k2_tarski(A_7, D_12)) | k2_tarski(A_7, D_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_803])).
% 3.01/1.63  tff(c_1141, plain, (![C_192, B_193]: (k4_tarski(C_192, B_193)!=B_193 | k2_tarski(B_193, B_193)=k1_xboole_0 | k2_tarski(B_193, B_193)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1091, c_811])).
% 3.01/1.63  tff(c_1144, plain, (k2_tarski('#skF_8', '#skF_8')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_720, c_1141])).
% 3.01/1.63  tff(c_1172, plain, (r2_hidden('#skF_8', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1144, c_22])).
% 3.01/1.63  tff(c_1186, plain, $false, inference(negUnitSimplification, [status(thm)], [c_910, c_1172])).
% 3.01/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.01/1.63  
% 3.01/1.63  Inference rules
% 3.01/1.63  ----------------------
% 3.01/1.63  #Ref     : 0
% 3.01/1.63  #Sup     : 277
% 3.01/1.63  #Fact    : 4
% 3.01/1.63  #Define  : 0
% 3.01/1.63  #Split   : 1
% 3.01/1.63  #Chain   : 0
% 3.01/1.63  #Close   : 0
% 3.01/1.63  
% 3.01/1.63  Ordering : KBO
% 3.01/1.63  
% 3.01/1.63  Simplification rules
% 3.01/1.63  ----------------------
% 3.01/1.63  #Subsume      : 49
% 3.01/1.63  #Demod        : 54
% 3.01/1.63  #Tautology    : 112
% 3.01/1.63  #SimpNegUnit  : 9
% 3.01/1.63  #BackRed      : 5
% 3.01/1.63  
% 3.01/1.63  #Partial instantiations: 0
% 3.01/1.63  #Strategies tried      : 1
% 3.01/1.63  
% 3.01/1.63  Timing (in seconds)
% 3.01/1.63  ----------------------
% 3.01/1.63  Preprocessing        : 0.39
% 3.01/1.63  Parsing              : 0.21
% 3.01/1.63  CNF conversion       : 0.03
% 3.01/1.63  Main loop            : 0.38
% 3.01/1.63  Inferencing          : 0.14
% 3.01/1.63  Reduction            : 0.10
% 3.01/1.63  Demodulation         : 0.07
% 3.01/1.63  BG Simplification    : 0.02
% 3.01/1.63  Subsumption          : 0.07
% 3.01/1.63  Abstraction          : 0.03
% 3.01/1.63  MUC search           : 0.00
% 3.01/1.63  Cooper               : 0.00
% 3.01/1.63  Total                : 0.80
% 3.01/1.63  Index Insertion      : 0.00
% 3.01/1.63  Index Deletion       : 0.00
% 3.01/1.63  Index Matching       : 0.00
% 3.01/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
