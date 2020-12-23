%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:09 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 110 expanded)
%              Number of leaves         :   33 (  54 expanded)
%              Depth                    :    7
%              Number of atoms          :   76 ( 148 expanded)
%              Number of equality atoms :   59 ( 118 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_9 > #skF_1 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_2 > #skF_7 > #skF_3 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_67,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_98,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_44,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_8,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_120,plain,(
    ! [A_74,B_75] : k2_xboole_0(k1_tarski(A_74),B_75) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_124,plain,(
    ! [A_74] : k1_tarski(A_74) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_120])).

tff(c_74,plain,(
    ! [A_58] :
      ( r2_hidden('#skF_9'(A_58),A_58)
      | k1_xboole_0 = A_58 ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_28,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_557,plain,(
    ! [D_157,B_158,A_159] :
      ( D_157 = B_158
      | D_157 = A_159
      | ~ r2_hidden(D_157,k2_tarski(A_159,B_158)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_609,plain,(
    ! [D_166,A_167] :
      ( D_166 = A_167
      | D_166 = A_167
      | ~ r2_hidden(D_166,k1_tarski(A_167)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_557])).

tff(c_613,plain,(
    ! [A_167] :
      ( '#skF_9'(k1_tarski(A_167)) = A_167
      | k1_tarski(A_167) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_74,c_609])).

tff(c_619,plain,(
    ! [A_167] : '#skF_9'(k1_tarski(A_167)) = A_167 ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_613])).

tff(c_431,plain,(
    ! [D_129,B_130] : r2_hidden(D_129,k2_tarski(D_129,B_130)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_434,plain,(
    ! [A_10] : r2_hidden(A_10,k1_tarski(A_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_431])).

tff(c_660,plain,(
    ! [D_174,A_175,C_176] :
      ( ~ r2_hidden(D_174,A_175)
      | k4_tarski(C_176,D_174) != '#skF_9'(A_175)
      | k1_xboole_0 = A_175 ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_666,plain,(
    ! [C_176,A_10] :
      ( k4_tarski(C_176,A_10) != '#skF_9'(k1_tarski(A_10))
      | k1_tarski(A_10) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_434,c_660])).

tff(c_672,plain,(
    ! [C_176,A_10] :
      ( k4_tarski(C_176,A_10) != A_10
      | k1_tarski(A_10) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_619,c_666])).

tff(c_673,plain,(
    ! [C_176,A_10] : k4_tarski(C_176,A_10) != A_10 ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_672])).

tff(c_82,plain,(
    k4_tarski('#skF_11','#skF_12') = '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_135,plain,(
    ! [A_78,B_79] : k2_mcart_1(k4_tarski(A_78,B_79)) = B_79 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_144,plain,(
    k2_mcart_1('#skF_10') = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_135])).

tff(c_312,plain,(
    ! [D_112,B_113,A_114] :
      ( D_112 = B_113
      | D_112 = A_114
      | ~ r2_hidden(D_112,k2_tarski(A_114,B_113)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_331,plain,(
    ! [D_115,A_116] :
      ( D_115 = A_116
      | D_115 = A_116
      | ~ r2_hidden(D_115,k1_tarski(A_116)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_312])).

tff(c_335,plain,(
    ! [A_116] :
      ( '#skF_9'(k1_tarski(A_116)) = A_116
      | k1_tarski(A_116) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_74,c_331])).

tff(c_341,plain,(
    ! [A_116] : '#skF_9'(k1_tarski(A_116)) = A_116 ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_335])).

tff(c_156,plain,(
    ! [D_80,A_81] : r2_hidden(D_80,k2_tarski(A_81,D_80)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_159,plain,(
    ! [A_10] : r2_hidden(A_10,k1_tarski(A_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_156])).

tff(c_388,plain,(
    ! [C_124,A_125,D_126] :
      ( ~ r2_hidden(C_124,A_125)
      | k4_tarski(C_124,D_126) != '#skF_9'(A_125)
      | k1_xboole_0 = A_125 ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_394,plain,(
    ! [A_10,D_126] :
      ( k4_tarski(A_10,D_126) != '#skF_9'(k1_tarski(A_10))
      | k1_tarski(A_10) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_159,c_388])).

tff(c_400,plain,(
    ! [A_10,D_126] :
      ( k4_tarski(A_10,D_126) != A_10
      | k1_tarski(A_10) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_394])).

tff(c_401,plain,(
    ! [A_10,D_126] : k4_tarski(A_10,D_126) != A_10 ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_400])).

tff(c_80,plain,
    ( k2_mcart_1('#skF_10') = '#skF_10'
    | k1_mcart_1('#skF_10') = '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_147,plain,(
    k1_mcart_1('#skF_10') = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_161,plain,(
    ! [A_83,B_84] : k1_mcart_1(k4_tarski(A_83,B_84)) = A_83 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_170,plain,(
    k1_mcart_1('#skF_10') = '#skF_11' ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_161])).

tff(c_173,plain,(
    '#skF_11' = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_170])).

tff(c_179,plain,(
    k4_tarski('#skF_10','#skF_12') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_82])).

tff(c_408,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_401,c_179])).

tff(c_409,plain,(
    k2_mcart_1('#skF_10') = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_415,plain,(
    '#skF_10' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_409])).

tff(c_422,plain,(
    k4_tarski('#skF_11','#skF_12') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_82])).

tff(c_676,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_673,c_422])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:19:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.35  
% 2.31/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.35  %$ r2_hidden > r1_tarski > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_9 > #skF_1 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_2 > #skF_7 > #skF_3 > #skF_12
% 2.31/1.35  
% 2.31/1.35  %Foreground sorts:
% 2.31/1.35  
% 2.31/1.35  
% 2.31/1.35  %Background operators:
% 2.31/1.35  
% 2.31/1.35  
% 2.31/1.35  %Foreground operators:
% 2.31/1.35  tff('#skF_9', type, '#skF_9': $i > $i).
% 2.31/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.31/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.31/1.35  tff('#skF_11', type, '#skF_11': $i).
% 2.31/1.35  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.31/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.31/1.35  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.31/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.31/1.35  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.31/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.31/1.35  tff('#skF_10', type, '#skF_10': $i).
% 2.31/1.35  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 2.31/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.31/1.35  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.31/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.31/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.31/1.35  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 2.31/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.35  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.31/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.31/1.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.31/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.35  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.31/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.31/1.35  tff('#skF_12', type, '#skF_12': $i).
% 2.31/1.35  
% 2.31/1.37  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.31/1.37  tff(f_67, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.31/1.37  tff(f_98, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.31/1.37  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.31/1.37  tff(f_42, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.31/1.37  tff(f_108, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.31/1.37  tff(f_82, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.31/1.37  tff(c_8, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.31/1.37  tff(c_120, plain, (![A_74, B_75]: (k2_xboole_0(k1_tarski(A_74), B_75)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.31/1.37  tff(c_124, plain, (![A_74]: (k1_tarski(A_74)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_120])).
% 2.31/1.37  tff(c_74, plain, (![A_58]: (r2_hidden('#skF_9'(A_58), A_58) | k1_xboole_0=A_58)), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.31/1.37  tff(c_28, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.31/1.37  tff(c_557, plain, (![D_157, B_158, A_159]: (D_157=B_158 | D_157=A_159 | ~r2_hidden(D_157, k2_tarski(A_159, B_158)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.31/1.37  tff(c_609, plain, (![D_166, A_167]: (D_166=A_167 | D_166=A_167 | ~r2_hidden(D_166, k1_tarski(A_167)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_557])).
% 2.31/1.37  tff(c_613, plain, (![A_167]: ('#skF_9'(k1_tarski(A_167))=A_167 | k1_tarski(A_167)=k1_xboole_0)), inference(resolution, [status(thm)], [c_74, c_609])).
% 2.31/1.37  tff(c_619, plain, (![A_167]: ('#skF_9'(k1_tarski(A_167))=A_167)), inference(negUnitSimplification, [status(thm)], [c_124, c_613])).
% 2.31/1.37  tff(c_431, plain, (![D_129, B_130]: (r2_hidden(D_129, k2_tarski(D_129, B_130)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.31/1.37  tff(c_434, plain, (![A_10]: (r2_hidden(A_10, k1_tarski(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_431])).
% 2.31/1.37  tff(c_660, plain, (![D_174, A_175, C_176]: (~r2_hidden(D_174, A_175) | k4_tarski(C_176, D_174)!='#skF_9'(A_175) | k1_xboole_0=A_175)), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.31/1.37  tff(c_666, plain, (![C_176, A_10]: (k4_tarski(C_176, A_10)!='#skF_9'(k1_tarski(A_10)) | k1_tarski(A_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_434, c_660])).
% 2.31/1.37  tff(c_672, plain, (![C_176, A_10]: (k4_tarski(C_176, A_10)!=A_10 | k1_tarski(A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_619, c_666])).
% 2.31/1.37  tff(c_673, plain, (![C_176, A_10]: (k4_tarski(C_176, A_10)!=A_10)), inference(negUnitSimplification, [status(thm)], [c_124, c_672])).
% 2.31/1.37  tff(c_82, plain, (k4_tarski('#skF_11', '#skF_12')='#skF_10'), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.31/1.37  tff(c_135, plain, (![A_78, B_79]: (k2_mcart_1(k4_tarski(A_78, B_79))=B_79)), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.31/1.37  tff(c_144, plain, (k2_mcart_1('#skF_10')='#skF_12'), inference(superposition, [status(thm), theory('equality')], [c_82, c_135])).
% 2.31/1.37  tff(c_312, plain, (![D_112, B_113, A_114]: (D_112=B_113 | D_112=A_114 | ~r2_hidden(D_112, k2_tarski(A_114, B_113)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.31/1.37  tff(c_331, plain, (![D_115, A_116]: (D_115=A_116 | D_115=A_116 | ~r2_hidden(D_115, k1_tarski(A_116)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_312])).
% 2.31/1.37  tff(c_335, plain, (![A_116]: ('#skF_9'(k1_tarski(A_116))=A_116 | k1_tarski(A_116)=k1_xboole_0)), inference(resolution, [status(thm)], [c_74, c_331])).
% 2.31/1.37  tff(c_341, plain, (![A_116]: ('#skF_9'(k1_tarski(A_116))=A_116)), inference(negUnitSimplification, [status(thm)], [c_124, c_335])).
% 2.31/1.37  tff(c_156, plain, (![D_80, A_81]: (r2_hidden(D_80, k2_tarski(A_81, D_80)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.31/1.37  tff(c_159, plain, (![A_10]: (r2_hidden(A_10, k1_tarski(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_156])).
% 2.31/1.37  tff(c_388, plain, (![C_124, A_125, D_126]: (~r2_hidden(C_124, A_125) | k4_tarski(C_124, D_126)!='#skF_9'(A_125) | k1_xboole_0=A_125)), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.31/1.37  tff(c_394, plain, (![A_10, D_126]: (k4_tarski(A_10, D_126)!='#skF_9'(k1_tarski(A_10)) | k1_tarski(A_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_159, c_388])).
% 2.31/1.37  tff(c_400, plain, (![A_10, D_126]: (k4_tarski(A_10, D_126)!=A_10 | k1_tarski(A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_341, c_394])).
% 2.31/1.37  tff(c_401, plain, (![A_10, D_126]: (k4_tarski(A_10, D_126)!=A_10)), inference(negUnitSimplification, [status(thm)], [c_124, c_400])).
% 2.31/1.37  tff(c_80, plain, (k2_mcart_1('#skF_10')='#skF_10' | k1_mcart_1('#skF_10')='#skF_10'), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.31/1.37  tff(c_147, plain, (k1_mcart_1('#skF_10')='#skF_10'), inference(splitLeft, [status(thm)], [c_80])).
% 2.31/1.37  tff(c_161, plain, (![A_83, B_84]: (k1_mcart_1(k4_tarski(A_83, B_84))=A_83)), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.31/1.37  tff(c_170, plain, (k1_mcart_1('#skF_10')='#skF_11'), inference(superposition, [status(thm), theory('equality')], [c_82, c_161])).
% 2.31/1.37  tff(c_173, plain, ('#skF_11'='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_147, c_170])).
% 2.31/1.37  tff(c_179, plain, (k4_tarski('#skF_10', '#skF_12')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_173, c_82])).
% 2.31/1.37  tff(c_408, plain, $false, inference(negUnitSimplification, [status(thm)], [c_401, c_179])).
% 2.31/1.37  tff(c_409, plain, (k2_mcart_1('#skF_10')='#skF_10'), inference(splitRight, [status(thm)], [c_80])).
% 2.31/1.37  tff(c_415, plain, ('#skF_10'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_144, c_409])).
% 2.31/1.37  tff(c_422, plain, (k4_tarski('#skF_11', '#skF_12')='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_415, c_82])).
% 2.31/1.37  tff(c_676, plain, $false, inference(negUnitSimplification, [status(thm)], [c_673, c_422])).
% 2.31/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.37  
% 2.31/1.37  Inference rules
% 2.31/1.37  ----------------------
% 2.31/1.37  #Ref     : 0
% 2.31/1.37  #Sup     : 146
% 2.31/1.37  #Fact    : 0
% 2.31/1.37  #Define  : 0
% 2.31/1.37  #Split   : 3
% 2.31/1.37  #Chain   : 0
% 2.31/1.37  #Close   : 0
% 2.31/1.37  
% 2.31/1.37  Ordering : KBO
% 2.31/1.37  
% 2.31/1.37  Simplification rules
% 2.31/1.37  ----------------------
% 2.31/1.37  #Subsume      : 34
% 2.31/1.37  #Demod        : 22
% 2.31/1.37  #Tautology    : 69
% 2.31/1.37  #SimpNegUnit  : 16
% 2.31/1.37  #BackRed      : 8
% 2.31/1.37  
% 2.31/1.37  #Partial instantiations: 0
% 2.31/1.37  #Strategies tried      : 1
% 2.31/1.37  
% 2.31/1.37  Timing (in seconds)
% 2.31/1.37  ----------------------
% 2.31/1.37  Preprocessing        : 0.33
% 2.31/1.37  Parsing              : 0.17
% 2.31/1.37  CNF conversion       : 0.03
% 2.31/1.37  Main loop            : 0.27
% 2.31/1.37  Inferencing          : 0.09
% 2.31/1.37  Reduction            : 0.08
% 2.31/1.37  Demodulation         : 0.06
% 2.31/1.37  BG Simplification    : 0.02
% 2.31/1.37  Subsumption          : 0.05
% 2.31/1.37  Abstraction          : 0.02
% 2.31/1.37  MUC search           : 0.00
% 2.31/1.37  Cooper               : 0.00
% 2.31/1.37  Total                : 0.63
% 2.31/1.37  Index Insertion      : 0.00
% 2.31/1.37  Index Deletion       : 0.00
% 2.31/1.37  Index Matching       : 0.00
% 2.31/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
