%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:40 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :   73 (  93 expanded)
%              Number of leaves         :   31 (  44 expanded)
%              Depth                    :    7
%              Number of atoms          :   90 ( 132 expanded)
%              Number of equality atoms :   24 (  43 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

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

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_68,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_70,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_76,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_90,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_134,plain,(
    ! [A_58,B_59] :
      ( r1_xboole_0(k1_tarski(A_58),B_59)
      | r2_hidden(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_20,plain,(
    ! [B_8,A_7] :
      ( r1_xboole_0(B_8,A_7)
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_150,plain,(
    ! [B_62,A_63] :
      ( r1_xboole_0(B_62,k1_tarski(A_63))
      | r2_hidden(A_63,B_62) ) ),
    inference(resolution,[status(thm)],[c_134,c_20])).

tff(c_36,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = A_14
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_170,plain,(
    ! [B_74,A_75] :
      ( k4_xboole_0(B_74,k1_tarski(A_75)) = B_74
      | r2_hidden(A_75,B_74) ) ),
    inference(resolution,[status(thm)],[c_150,c_36])).

tff(c_74,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_114,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_178,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_114])).

tff(c_187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_178])).

tff(c_188,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_64,plain,(
    ! [A_23] : k2_tarski(A_23,A_23) = k1_tarski(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_96,plain,(
    ! [A_49,B_50] : k1_enumset1(A_49,A_49,B_50) = k2_tarski(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_46,plain,(
    ! [E_22,B_17,C_18] : r2_hidden(E_22,k1_enumset1(E_22,B_17,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_194,plain,(
    ! [A_76,B_77] : r2_hidden(A_76,k2_tarski(A_76,B_77)) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_46])).

tff(c_197,plain,(
    ! [A_23] : r2_hidden(A_23,k1_tarski(A_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_194])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k3_xboole_0(A_1,B_2))
      | ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_189,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_78,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_249,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_78])).

tff(c_34,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_398,plain,(
    ! [A_122,C_123,B_124] :
      ( ~ r2_hidden(A_122,C_123)
      | ~ r2_hidden(A_122,B_124)
      | ~ r2_hidden(A_122,k5_xboole_0(B_124,C_123)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_653,plain,(
    ! [A_146,A_147,B_148] :
      ( ~ r2_hidden(A_146,k3_xboole_0(A_147,B_148))
      | ~ r2_hidden(A_146,A_147)
      | ~ r2_hidden(A_146,k4_xboole_0(A_147,B_148)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_398])).

tff(c_696,plain,(
    ! [A_149] :
      ( ~ r2_hidden(A_149,k3_xboole_0('#skF_7',k1_tarski('#skF_8')))
      | ~ r2_hidden(A_149,'#skF_7')
      | ~ r2_hidden(A_149,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_653])).

tff(c_722,plain,(
    ! [D_150] :
      ( ~ r2_hidden(D_150,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_150,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_2,c_696])).

tff(c_742,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_197,c_722])).

tff(c_750,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_742])).

tff(c_751,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_759,plain,(
    ! [A_164,B_165] : k1_enumset1(A_164,A_164,B_165) = k2_tarski(A_164,B_165) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_44,plain,(
    ! [E_22,A_16,C_18] : r2_hidden(E_22,k1_enumset1(A_16,E_22,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_777,plain,(
    ! [A_166,B_167] : r2_hidden(A_166,k2_tarski(A_166,B_167)) ),
    inference(superposition,[status(thm),theory(equality)],[c_759,c_44])).

tff(c_780,plain,(
    ! [A_23] : r2_hidden(A_23,k1_tarski(A_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_777])).

tff(c_752,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_80,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_813,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_752,c_80])).

tff(c_951,plain,(
    ! [A_212,C_213,B_214] :
      ( ~ r2_hidden(A_212,C_213)
      | ~ r2_hidden(A_212,B_214)
      | ~ r2_hidden(A_212,k5_xboole_0(B_214,C_213)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1113,plain,(
    ! [A_233,A_234,B_235] :
      ( ~ r2_hidden(A_233,k3_xboole_0(A_234,B_235))
      | ~ r2_hidden(A_233,A_234)
      | ~ r2_hidden(A_233,k4_xboole_0(A_234,B_235)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_951])).

tff(c_1140,plain,(
    ! [A_236] :
      ( ~ r2_hidden(A_236,k3_xboole_0('#skF_7',k1_tarski('#skF_8')))
      | ~ r2_hidden(A_236,'#skF_7')
      | ~ r2_hidden(A_236,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_813,c_1113])).

tff(c_1182,plain,(
    ! [D_240] :
      ( ~ r2_hidden(D_240,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_240,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_2,c_1140])).

tff(c_1194,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_780,c_1182])).

tff(c_1200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_751,c_1194])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:44:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.49  
% 3.16/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.50  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 3.16/1.50  
% 3.16/1.50  %Foreground sorts:
% 3.16/1.50  
% 3.16/1.50  
% 3.16/1.50  %Background operators:
% 3.16/1.50  
% 3.16/1.50  
% 3.16/1.50  %Foreground operators:
% 3.16/1.50  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.16/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.16/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.16/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.16/1.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.16/1.50  tff('#skF_7', type, '#skF_7': $i).
% 3.16/1.50  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.16/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.16/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.16/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.16/1.50  tff('#skF_6', type, '#skF_6': $i).
% 3.16/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.16/1.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.16/1.50  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.16/1.50  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.16/1.50  tff('#skF_8', type, '#skF_8': $i).
% 3.16/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.16/1.50  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.16/1.50  
% 3.37/1.51  tff(f_85, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.37/1.51  tff(f_79, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.37/1.51  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.37/1.51  tff(f_51, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.37/1.51  tff(f_68, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.37/1.51  tff(f_70, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.37/1.51  tff(f_66, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.37/1.51  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.37/1.51  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.37/1.51  tff(f_45, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 3.37/1.51  tff(c_76, plain, (~r2_hidden('#skF_6', '#skF_5') | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.37/1.51  tff(c_90, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_76])).
% 3.37/1.51  tff(c_134, plain, (![A_58, B_59]: (r1_xboole_0(k1_tarski(A_58), B_59) | r2_hidden(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.37/1.51  tff(c_20, plain, (![B_8, A_7]: (r1_xboole_0(B_8, A_7) | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.37/1.51  tff(c_150, plain, (![B_62, A_63]: (r1_xboole_0(B_62, k1_tarski(A_63)) | r2_hidden(A_63, B_62))), inference(resolution, [status(thm)], [c_134, c_20])).
% 3.37/1.51  tff(c_36, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=A_14 | ~r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.37/1.51  tff(c_170, plain, (![B_74, A_75]: (k4_xboole_0(B_74, k1_tarski(A_75))=B_74 | r2_hidden(A_75, B_74))), inference(resolution, [status(thm)], [c_150, c_36])).
% 3.37/1.51  tff(c_74, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.37/1.51  tff(c_114, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_74])).
% 3.37/1.51  tff(c_178, plain, (r2_hidden('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_170, c_114])).
% 3.37/1.51  tff(c_187, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_178])).
% 3.37/1.51  tff(c_188, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_74])).
% 3.37/1.51  tff(c_64, plain, (![A_23]: (k2_tarski(A_23, A_23)=k1_tarski(A_23))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.37/1.51  tff(c_96, plain, (![A_49, B_50]: (k1_enumset1(A_49, A_49, B_50)=k2_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.37/1.51  tff(c_46, plain, (![E_22, B_17, C_18]: (r2_hidden(E_22, k1_enumset1(E_22, B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.37/1.51  tff(c_194, plain, (![A_76, B_77]: (r2_hidden(A_76, k2_tarski(A_76, B_77)))), inference(superposition, [status(thm), theory('equality')], [c_96, c_46])).
% 3.37/1.51  tff(c_197, plain, (![A_23]: (r2_hidden(A_23, k1_tarski(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_194])).
% 3.37/1.51  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k3_xboole_0(A_1, B_2)) | ~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.37/1.51  tff(c_189, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_74])).
% 3.37/1.51  tff(c_78, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.37/1.51  tff(c_249, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_189, c_78])).
% 3.37/1.51  tff(c_34, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.37/1.51  tff(c_398, plain, (![A_122, C_123, B_124]: (~r2_hidden(A_122, C_123) | ~r2_hidden(A_122, B_124) | ~r2_hidden(A_122, k5_xboole_0(B_124, C_123)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.37/1.51  tff(c_653, plain, (![A_146, A_147, B_148]: (~r2_hidden(A_146, k3_xboole_0(A_147, B_148)) | ~r2_hidden(A_146, A_147) | ~r2_hidden(A_146, k4_xboole_0(A_147, B_148)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_398])).
% 3.37/1.51  tff(c_696, plain, (![A_149]: (~r2_hidden(A_149, k3_xboole_0('#skF_7', k1_tarski('#skF_8'))) | ~r2_hidden(A_149, '#skF_7') | ~r2_hidden(A_149, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_249, c_653])).
% 3.37/1.51  tff(c_722, plain, (![D_150]: (~r2_hidden(D_150, k1_tarski('#skF_8')) | ~r2_hidden(D_150, '#skF_7'))), inference(resolution, [status(thm)], [c_2, c_696])).
% 3.37/1.51  tff(c_742, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_197, c_722])).
% 3.37/1.51  tff(c_750, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_188, c_742])).
% 3.37/1.51  tff(c_751, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_76])).
% 3.37/1.51  tff(c_759, plain, (![A_164, B_165]: (k1_enumset1(A_164, A_164, B_165)=k2_tarski(A_164, B_165))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.37/1.51  tff(c_44, plain, (![E_22, A_16, C_18]: (r2_hidden(E_22, k1_enumset1(A_16, E_22, C_18)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.37/1.51  tff(c_777, plain, (![A_166, B_167]: (r2_hidden(A_166, k2_tarski(A_166, B_167)))), inference(superposition, [status(thm), theory('equality')], [c_759, c_44])).
% 3.37/1.51  tff(c_780, plain, (![A_23]: (r2_hidden(A_23, k1_tarski(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_777])).
% 3.37/1.51  tff(c_752, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_76])).
% 3.37/1.51  tff(c_80, plain, (~r2_hidden('#skF_6', '#skF_5') | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.37/1.51  tff(c_813, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_752, c_80])).
% 3.37/1.51  tff(c_951, plain, (![A_212, C_213, B_214]: (~r2_hidden(A_212, C_213) | ~r2_hidden(A_212, B_214) | ~r2_hidden(A_212, k5_xboole_0(B_214, C_213)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.37/1.51  tff(c_1113, plain, (![A_233, A_234, B_235]: (~r2_hidden(A_233, k3_xboole_0(A_234, B_235)) | ~r2_hidden(A_233, A_234) | ~r2_hidden(A_233, k4_xboole_0(A_234, B_235)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_951])).
% 3.37/1.51  tff(c_1140, plain, (![A_236]: (~r2_hidden(A_236, k3_xboole_0('#skF_7', k1_tarski('#skF_8'))) | ~r2_hidden(A_236, '#skF_7') | ~r2_hidden(A_236, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_813, c_1113])).
% 3.37/1.51  tff(c_1182, plain, (![D_240]: (~r2_hidden(D_240, k1_tarski('#skF_8')) | ~r2_hidden(D_240, '#skF_7'))), inference(resolution, [status(thm)], [c_2, c_1140])).
% 3.37/1.51  tff(c_1194, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_780, c_1182])).
% 3.37/1.51  tff(c_1200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_751, c_1194])).
% 3.37/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.51  
% 3.37/1.51  Inference rules
% 3.37/1.51  ----------------------
% 3.37/1.51  #Ref     : 0
% 3.37/1.51  #Sup     : 251
% 3.37/1.51  #Fact    : 0
% 3.37/1.51  #Define  : 0
% 3.37/1.51  #Split   : 2
% 3.37/1.51  #Chain   : 0
% 3.37/1.51  #Close   : 0
% 3.37/1.51  
% 3.37/1.51  Ordering : KBO
% 3.37/1.51  
% 3.37/1.51  Simplification rules
% 3.37/1.51  ----------------------
% 3.37/1.51  #Subsume      : 14
% 3.37/1.51  #Demod        : 23
% 3.37/1.51  #Tautology    : 121
% 3.37/1.51  #SimpNegUnit  : 5
% 3.37/1.51  #BackRed      : 0
% 3.37/1.51  
% 3.37/1.51  #Partial instantiations: 0
% 3.37/1.51  #Strategies tried      : 1
% 3.37/1.51  
% 3.37/1.51  Timing (in seconds)
% 3.37/1.51  ----------------------
% 3.37/1.52  Preprocessing        : 0.32
% 3.37/1.52  Parsing              : 0.16
% 3.37/1.52  CNF conversion       : 0.03
% 3.37/1.52  Main loop            : 0.44
% 3.37/1.52  Inferencing          : 0.16
% 3.37/1.52  Reduction            : 0.12
% 3.37/1.52  Demodulation         : 0.09
% 3.37/1.52  BG Simplification    : 0.03
% 3.37/1.52  Subsumption          : 0.09
% 3.37/1.52  Abstraction          : 0.03
% 3.37/1.52  MUC search           : 0.00
% 3.37/1.52  Cooper               : 0.00
% 3.37/1.52  Total                : 0.79
% 3.37/1.52  Index Insertion      : 0.00
% 3.37/1.52  Index Deletion       : 0.00
% 3.37/1.52  Index Matching       : 0.00
% 3.37/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
