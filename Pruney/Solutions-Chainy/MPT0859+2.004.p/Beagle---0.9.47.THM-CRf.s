%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:58 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 117 expanded)
%              Number of leaves         :   30 (  51 expanded)
%              Depth                    :    7
%              Number of atoms          :   87 ( 213 expanded)
%              Number of equality atoms :   22 (  59 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),D))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & r2_hidden(k2_mcart_1(A),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_mcart_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C)
        & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_85,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

tff(c_60,plain,
    ( k1_mcart_1('#skF_3') != '#skF_5'
    | ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_101,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_58,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_159,plain,(
    ! [A_68,C_69,B_70] :
      ( r2_hidden(k2_mcart_1(A_68),C_69)
      | ~ r2_hidden(A_68,k2_zfmisc_1(B_70,C_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_161,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_159])).

tff(c_165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_161])).

tff(c_166,plain,(
    k1_mcart_1('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_167,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_62,plain,
    ( k1_mcart_1('#skF_3') != '#skF_4'
    | ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_169,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_62])).

tff(c_26,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_170,plain,(
    ! [B_71,C_72,A_73] :
      ( r2_hidden(B_71,C_72)
      | ~ r1_tarski(k2_tarski(A_73,B_71),C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_179,plain,(
    ! [B_74,A_75] : r2_hidden(B_74,k2_tarski(A_75,B_74)) ),
    inference(resolution,[status(thm)],[c_24,c_170])).

tff(c_182,plain,(
    ! [A_9] : r2_hidden(A_9,k1_tarski(A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_179])).

tff(c_214,plain,(
    ! [A_92,B_93,C_94] :
      ( r2_hidden(k1_mcart_1(A_92),B_93)
      | ~ r2_hidden(A_92,k2_zfmisc_1(B_93,C_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_217,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_58,c_214])).

tff(c_259,plain,(
    ! [C_118,A_119,B_120] :
      ( k4_xboole_0(C_118,k2_tarski(A_119,B_120)) = C_118
      | r2_hidden(B_120,C_118)
      | r2_hidden(A_119,C_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_391,plain,(
    ! [D_141,A_142,B_143,C_144] :
      ( ~ r2_hidden(D_141,k2_tarski(A_142,B_143))
      | ~ r2_hidden(D_141,C_144)
      | r2_hidden(B_143,C_144)
      | r2_hidden(A_142,C_144) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_4])).

tff(c_403,plain,(
    ! [C_145] :
      ( ~ r2_hidden(k1_mcart_1('#skF_3'),C_145)
      | r2_hidden('#skF_5',C_145)
      | r2_hidden('#skF_4',C_145) ) ),
    inference(resolution,[status(thm)],[c_217,c_391])).

tff(c_427,plain,
    ( r2_hidden('#skF_5',k1_tarski(k1_mcart_1('#skF_3')))
    | r2_hidden('#skF_4',k1_tarski(k1_mcart_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_182,c_403])).

tff(c_429,plain,(
    r2_hidden('#skF_4',k1_tarski(k1_mcart_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_427])).

tff(c_54,plain,(
    ! [A_31,B_32] : k1_mcart_1(k4_tarski(A_31,B_32)) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_325,plain,(
    ! [A_127,B_128,C_129,D_130] :
      ( r2_hidden(k4_tarski(A_127,B_128),k2_zfmisc_1(C_129,D_130))
      | ~ r2_hidden(B_128,D_130)
      | ~ r2_hidden(A_127,C_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_52,plain,(
    ! [A_28,B_29,C_30] :
      ( k1_mcart_1(A_28) = B_29
      | ~ r2_hidden(A_28,k2_zfmisc_1(k1_tarski(B_29),C_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_337,plain,(
    ! [A_127,B_128,B_29,D_130] :
      ( k1_mcart_1(k4_tarski(A_127,B_128)) = B_29
      | ~ r2_hidden(B_128,D_130)
      | ~ r2_hidden(A_127,k1_tarski(B_29)) ) ),
    inference(resolution,[status(thm)],[c_325,c_52])).

tff(c_345,plain,(
    ! [B_29,A_127,B_128,D_130] :
      ( B_29 = A_127
      | ~ r2_hidden(B_128,D_130)
      | ~ r2_hidden(A_127,k1_tarski(B_29)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_337])).

tff(c_348,plain,(
    ! [B_128,D_130] : ~ r2_hidden(B_128,D_130) ),
    inference(splitLeft,[status(thm)],[c_345])).

tff(c_367,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_348,c_217])).

tff(c_368,plain,(
    ! [B_29,A_127] :
      ( B_29 = A_127
      | ~ r2_hidden(A_127,k1_tarski(B_29)) ) ),
    inference(splitRight,[status(thm)],[c_345])).

tff(c_445,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_429,c_368])).

tff(c_451,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_445])).

tff(c_452,plain,(
    r2_hidden('#skF_5',k1_tarski(k1_mcart_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_427])).

tff(c_460,plain,(
    k1_mcart_1('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_452,c_368])).

tff(c_466,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_460])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:51:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.34  
% 2.65/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.34  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 2.65/1.34  
% 2.65/1.34  %Foreground sorts:
% 2.65/1.34  
% 2.65/1.34  
% 2.65/1.34  %Background operators:
% 2.65/1.34  
% 2.65/1.34  
% 2.65/1.34  %Foreground operators:
% 2.65/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.65/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.65/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.65/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.65/1.34  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.65/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.65/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.65/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.65/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.65/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.65/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.65/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.65/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.65/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.34  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.65/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.65/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.65/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.34  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.65/1.34  
% 2.65/1.36  tff(f_94, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), D)) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & r2_hidden(k2_mcart_1(A), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_mcart_1)).
% 2.65/1.36  tff(f_75, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.65/1.36  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.65/1.36  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.65/1.36  tff(f_69, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.65/1.36  tff(f_63, axiom, (![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 2.65/1.36  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.65/1.36  tff(f_85, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.65/1.36  tff(f_53, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.65/1.36  tff(f_81, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_mcart_1)).
% 2.65/1.36  tff(c_60, plain, (k1_mcart_1('#skF_3')!='#skF_5' | ~r2_hidden(k2_mcart_1('#skF_3'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.65/1.36  tff(c_101, plain, (~r2_hidden(k2_mcart_1('#skF_3'), '#skF_6')), inference(splitLeft, [status(thm)], [c_60])).
% 2.65/1.36  tff(c_58, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.65/1.36  tff(c_159, plain, (![A_68, C_69, B_70]: (r2_hidden(k2_mcart_1(A_68), C_69) | ~r2_hidden(A_68, k2_zfmisc_1(B_70, C_69)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.65/1.36  tff(c_161, plain, (r2_hidden(k2_mcart_1('#skF_3'), '#skF_6')), inference(resolution, [status(thm)], [c_58, c_159])).
% 2.65/1.36  tff(c_165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_101, c_161])).
% 2.65/1.36  tff(c_166, plain, (k1_mcart_1('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_60])).
% 2.65/1.36  tff(c_167, plain, (r2_hidden(k2_mcart_1('#skF_3'), '#skF_6')), inference(splitRight, [status(thm)], [c_60])).
% 2.65/1.36  tff(c_62, plain, (k1_mcart_1('#skF_3')!='#skF_4' | ~r2_hidden(k2_mcart_1('#skF_3'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.65/1.36  tff(c_169, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_167, c_62])).
% 2.65/1.36  tff(c_26, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.65/1.36  tff(c_24, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.65/1.36  tff(c_170, plain, (![B_71, C_72, A_73]: (r2_hidden(B_71, C_72) | ~r1_tarski(k2_tarski(A_73, B_71), C_72))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.65/1.36  tff(c_179, plain, (![B_74, A_75]: (r2_hidden(B_74, k2_tarski(A_75, B_74)))), inference(resolution, [status(thm)], [c_24, c_170])).
% 2.65/1.36  tff(c_182, plain, (![A_9]: (r2_hidden(A_9, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_179])).
% 2.65/1.36  tff(c_214, plain, (![A_92, B_93, C_94]: (r2_hidden(k1_mcart_1(A_92), B_93) | ~r2_hidden(A_92, k2_zfmisc_1(B_93, C_94)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.65/1.36  tff(c_217, plain, (r2_hidden(k1_mcart_1('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_58, c_214])).
% 2.65/1.36  tff(c_259, plain, (![C_118, A_119, B_120]: (k4_xboole_0(C_118, k2_tarski(A_119, B_120))=C_118 | r2_hidden(B_120, C_118) | r2_hidden(A_119, C_118))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.65/1.36  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.65/1.36  tff(c_391, plain, (![D_141, A_142, B_143, C_144]: (~r2_hidden(D_141, k2_tarski(A_142, B_143)) | ~r2_hidden(D_141, C_144) | r2_hidden(B_143, C_144) | r2_hidden(A_142, C_144))), inference(superposition, [status(thm), theory('equality')], [c_259, c_4])).
% 2.65/1.36  tff(c_403, plain, (![C_145]: (~r2_hidden(k1_mcart_1('#skF_3'), C_145) | r2_hidden('#skF_5', C_145) | r2_hidden('#skF_4', C_145))), inference(resolution, [status(thm)], [c_217, c_391])).
% 2.65/1.36  tff(c_427, plain, (r2_hidden('#skF_5', k1_tarski(k1_mcart_1('#skF_3'))) | r2_hidden('#skF_4', k1_tarski(k1_mcart_1('#skF_3')))), inference(resolution, [status(thm)], [c_182, c_403])).
% 2.65/1.36  tff(c_429, plain, (r2_hidden('#skF_4', k1_tarski(k1_mcart_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_427])).
% 2.65/1.36  tff(c_54, plain, (![A_31, B_32]: (k1_mcart_1(k4_tarski(A_31, B_32))=A_31)), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.65/1.36  tff(c_325, plain, (![A_127, B_128, C_129, D_130]: (r2_hidden(k4_tarski(A_127, B_128), k2_zfmisc_1(C_129, D_130)) | ~r2_hidden(B_128, D_130) | ~r2_hidden(A_127, C_129))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.65/1.36  tff(c_52, plain, (![A_28, B_29, C_30]: (k1_mcart_1(A_28)=B_29 | ~r2_hidden(A_28, k2_zfmisc_1(k1_tarski(B_29), C_30)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.65/1.36  tff(c_337, plain, (![A_127, B_128, B_29, D_130]: (k1_mcart_1(k4_tarski(A_127, B_128))=B_29 | ~r2_hidden(B_128, D_130) | ~r2_hidden(A_127, k1_tarski(B_29)))), inference(resolution, [status(thm)], [c_325, c_52])).
% 2.65/1.36  tff(c_345, plain, (![B_29, A_127, B_128, D_130]: (B_29=A_127 | ~r2_hidden(B_128, D_130) | ~r2_hidden(A_127, k1_tarski(B_29)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_337])).
% 2.65/1.36  tff(c_348, plain, (![B_128, D_130]: (~r2_hidden(B_128, D_130))), inference(splitLeft, [status(thm)], [c_345])).
% 2.65/1.36  tff(c_367, plain, $false, inference(negUnitSimplification, [status(thm)], [c_348, c_217])).
% 2.65/1.36  tff(c_368, plain, (![B_29, A_127]: (B_29=A_127 | ~r2_hidden(A_127, k1_tarski(B_29)))), inference(splitRight, [status(thm)], [c_345])).
% 2.65/1.36  tff(c_445, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_429, c_368])).
% 2.65/1.36  tff(c_451, plain, $false, inference(negUnitSimplification, [status(thm)], [c_169, c_445])).
% 2.65/1.36  tff(c_452, plain, (r2_hidden('#skF_5', k1_tarski(k1_mcart_1('#skF_3')))), inference(splitRight, [status(thm)], [c_427])).
% 2.65/1.36  tff(c_460, plain, (k1_mcart_1('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_452, c_368])).
% 2.65/1.36  tff(c_466, plain, $false, inference(negUnitSimplification, [status(thm)], [c_166, c_460])).
% 2.65/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.36  
% 2.65/1.36  Inference rules
% 2.65/1.36  ----------------------
% 2.65/1.36  #Ref     : 0
% 2.65/1.36  #Sup     : 80
% 2.65/1.36  #Fact    : 0
% 2.65/1.36  #Define  : 0
% 2.65/1.36  #Split   : 3
% 2.65/1.36  #Chain   : 0
% 2.65/1.36  #Close   : 0
% 2.65/1.36  
% 2.65/1.36  Ordering : KBO
% 2.65/1.36  
% 2.65/1.36  Simplification rules
% 2.65/1.36  ----------------------
% 2.65/1.36  #Subsume      : 17
% 2.65/1.36  #Demod        : 17
% 2.65/1.36  #Tautology    : 44
% 2.65/1.36  #SimpNegUnit  : 21
% 2.65/1.36  #BackRed      : 11
% 2.65/1.36  
% 2.65/1.36  #Partial instantiations: 0
% 2.65/1.36  #Strategies tried      : 1
% 2.65/1.36  
% 2.65/1.36  Timing (in seconds)
% 2.65/1.36  ----------------------
% 2.65/1.36  Preprocessing        : 0.33
% 2.65/1.36  Parsing              : 0.16
% 2.65/1.36  CNF conversion       : 0.03
% 2.65/1.36  Main loop            : 0.27
% 2.65/1.36  Inferencing          : 0.10
% 2.65/1.36  Reduction            : 0.08
% 2.65/1.36  Demodulation         : 0.06
% 2.65/1.36  BG Simplification    : 0.02
% 2.65/1.36  Subsumption          : 0.05
% 2.65/1.36  Abstraction          : 0.02
% 2.65/1.36  MUC search           : 0.00
% 2.65/1.36  Cooper               : 0.00
% 2.65/1.36  Total                : 0.64
% 2.65/1.36  Index Insertion      : 0.00
% 2.65/1.36  Index Deletion       : 0.00
% 2.65/1.36  Index Matching       : 0.00
% 2.65/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
