%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:58 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 123 expanded)
%              Number of leaves         :   36 (  57 expanded)
%              Depth                    :    7
%              Number of atoms          :   89 ( 219 expanded)
%              Number of equality atoms :   24 (  65 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_2 > #skF_7 > #skF_9 > #skF_3 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_100,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),D))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & r2_hidden(k2_mcart_1(A),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C)
        & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_91,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

tff(c_78,plain,
    ( k1_mcart_1('#skF_9') != '#skF_11'
    | ~ r2_hidden(k2_mcart_1('#skF_9'),'#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_110,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_9'),'#skF_12') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_76,plain,(
    r2_hidden('#skF_9',k2_zfmisc_1(k2_tarski('#skF_10','#skF_11'),'#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_177,plain,(
    ! [A_98,C_99,B_100] :
      ( r2_hidden(k2_mcart_1(A_98),C_99)
      | ~ r2_hidden(A_98,k2_zfmisc_1(B_100,C_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_179,plain,(
    r2_hidden(k2_mcart_1('#skF_9'),'#skF_12') ),
    inference(resolution,[status(thm)],[c_76,c_177])).

tff(c_183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_179])).

tff(c_184,plain,(
    k1_mcart_1('#skF_9') != '#skF_11' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_185,plain,(
    r2_hidden(k2_mcart_1('#skF_9'),'#skF_12') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_80,plain,
    ( k1_mcart_1('#skF_9') != '#skF_10'
    | ~ r2_hidden(k2_mcart_1('#skF_9'),'#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_187,plain,(
    k1_mcart_1('#skF_9') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_80])).

tff(c_26,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_197,plain,(
    ! [A_103,C_104,B_105] :
      ( r2_hidden(A_103,C_104)
      | ~ r1_tarski(k2_tarski(A_103,B_105),C_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_206,plain,(
    ! [A_106,B_107] : r2_hidden(A_106,k2_tarski(A_106,B_107)) ),
    inference(resolution,[status(thm)],[c_24,c_197])).

tff(c_209,plain,(
    ! [A_9] : r2_hidden(A_9,k1_tarski(A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_206])).

tff(c_256,plain,(
    ! [A_133,B_134,C_135] :
      ( r2_hidden(k1_mcart_1(A_133),B_134)
      | ~ r2_hidden(A_133,k2_zfmisc_1(B_134,C_135)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_259,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k2_tarski('#skF_10','#skF_11')) ),
    inference(resolution,[status(thm)],[c_76,c_256])).

tff(c_311,plain,(
    ! [C_146,A_147,B_148] :
      ( k4_xboole_0(C_146,k2_tarski(A_147,B_148)) = C_146
      | r2_hidden(B_148,C_146)
      | r2_hidden(A_147,C_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_482,plain,(
    ! [D_171,A_172,B_173,C_174] :
      ( ~ r2_hidden(D_171,k2_tarski(A_172,B_173))
      | ~ r2_hidden(D_171,C_174)
      | r2_hidden(B_173,C_174)
      | r2_hidden(A_172,C_174) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_4])).

tff(c_502,plain,(
    ! [C_175] :
      ( ~ r2_hidden(k1_mcart_1('#skF_9'),C_175)
      | r2_hidden('#skF_11',C_175)
      | r2_hidden('#skF_10',C_175) ) ),
    inference(resolution,[status(thm)],[c_259,c_482])).

tff(c_526,plain,
    ( r2_hidden('#skF_11',k1_tarski(k1_mcart_1('#skF_9')))
    | r2_hidden('#skF_10',k1_tarski(k1_mcart_1('#skF_9'))) ),
    inference(resolution,[status(thm)],[c_209,c_502])).

tff(c_528,plain,(
    r2_hidden('#skF_10',k1_tarski(k1_mcart_1('#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_526])).

tff(c_72,plain,(
    ! [A_61,B_62] : k1_mcart_1(k4_tarski(A_61,B_62)) = A_61 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_357,plain,(
    ! [E_153,F_154,A_155,B_156] :
      ( r2_hidden(k4_tarski(E_153,F_154),k2_zfmisc_1(A_155,B_156))
      | ~ r2_hidden(F_154,B_156)
      | ~ r2_hidden(E_153,A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_70,plain,(
    ! [A_58,B_59,C_60] :
      ( k1_mcart_1(A_58) = B_59
      | ~ r2_hidden(A_58,k2_zfmisc_1(k1_tarski(B_59),C_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_365,plain,(
    ! [E_153,F_154,B_59,B_156] :
      ( k1_mcart_1(k4_tarski(E_153,F_154)) = B_59
      | ~ r2_hidden(F_154,B_156)
      | ~ r2_hidden(E_153,k1_tarski(B_59)) ) ),
    inference(resolution,[status(thm)],[c_357,c_70])).

tff(c_371,plain,(
    ! [E_153,B_59,F_154,B_156] :
      ( E_153 = B_59
      | ~ r2_hidden(F_154,B_156)
      | ~ r2_hidden(E_153,k1_tarski(B_59)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_365])).

tff(c_400,plain,(
    ! [F_154,B_156] : ~ r2_hidden(F_154,B_156) ),
    inference(splitLeft,[status(thm)],[c_371])).

tff(c_418,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_400,c_259])).

tff(c_419,plain,(
    ! [E_153,B_59] :
      ( E_153 = B_59
      | ~ r2_hidden(E_153,k1_tarski(B_59)) ) ),
    inference(splitRight,[status(thm)],[c_371])).

tff(c_542,plain,(
    k1_mcart_1('#skF_9') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_528,c_419])).

tff(c_549,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_542])).

tff(c_550,plain,(
    r2_hidden('#skF_11',k1_tarski(k1_mcart_1('#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_526])).

tff(c_556,plain,(
    k1_mcart_1('#skF_9') = '#skF_11' ),
    inference(resolution,[status(thm)],[c_550,c_419])).

tff(c_563,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_184,c_556])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:17:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.38  
% 2.71/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.38  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_2 > #skF_7 > #skF_9 > #skF_3 > #skF_12
% 2.71/1.38  
% 2.71/1.38  %Foreground sorts:
% 2.71/1.38  
% 2.71/1.38  
% 2.71/1.38  %Background operators:
% 2.71/1.38  
% 2.71/1.38  
% 2.71/1.38  %Foreground operators:
% 2.71/1.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.71/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.71/1.38  tff('#skF_11', type, '#skF_11': $i).
% 2.71/1.38  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.71/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.71/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.71/1.38  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.71/1.38  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.71/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.71/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.71/1.38  tff('#skF_10', type, '#skF_10': $i).
% 2.71/1.38  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 2.71/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.71/1.38  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.71/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.71/1.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.71/1.38  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 2.71/1.38  tff('#skF_9', type, '#skF_9': $i).
% 2.71/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.38  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.71/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.71/1.38  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.71/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.38  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.71/1.38  tff('#skF_12', type, '#skF_12': $i).
% 2.71/1.38  
% 2.71/1.39  tff(f_100, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), D)) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & r2_hidden(k2_mcart_1(A), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_mcart_1)).
% 2.71/1.39  tff(f_81, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.71/1.39  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.71/1.39  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.71/1.39  tff(f_75, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.71/1.39  tff(f_69, axiom, (![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 2.71/1.39  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.71/1.39  tff(f_91, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.71/1.39  tff(f_59, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 2.71/1.39  tff(f_87, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_mcart_1)).
% 2.71/1.39  tff(c_78, plain, (k1_mcart_1('#skF_9')!='#skF_11' | ~r2_hidden(k2_mcart_1('#skF_9'), '#skF_12')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.71/1.39  tff(c_110, plain, (~r2_hidden(k2_mcart_1('#skF_9'), '#skF_12')), inference(splitLeft, [status(thm)], [c_78])).
% 2.71/1.39  tff(c_76, plain, (r2_hidden('#skF_9', k2_zfmisc_1(k2_tarski('#skF_10', '#skF_11'), '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.71/1.39  tff(c_177, plain, (![A_98, C_99, B_100]: (r2_hidden(k2_mcart_1(A_98), C_99) | ~r2_hidden(A_98, k2_zfmisc_1(B_100, C_99)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.71/1.39  tff(c_179, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_12')), inference(resolution, [status(thm)], [c_76, c_177])).
% 2.71/1.39  tff(c_183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_179])).
% 2.71/1.39  tff(c_184, plain, (k1_mcart_1('#skF_9')!='#skF_11'), inference(splitRight, [status(thm)], [c_78])).
% 2.71/1.39  tff(c_185, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_12')), inference(splitRight, [status(thm)], [c_78])).
% 2.71/1.39  tff(c_80, plain, (k1_mcart_1('#skF_9')!='#skF_10' | ~r2_hidden(k2_mcart_1('#skF_9'), '#skF_12')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.71/1.39  tff(c_187, plain, (k1_mcart_1('#skF_9')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_185, c_80])).
% 2.71/1.39  tff(c_26, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.71/1.39  tff(c_24, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.71/1.39  tff(c_197, plain, (![A_103, C_104, B_105]: (r2_hidden(A_103, C_104) | ~r1_tarski(k2_tarski(A_103, B_105), C_104))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.71/1.39  tff(c_206, plain, (![A_106, B_107]: (r2_hidden(A_106, k2_tarski(A_106, B_107)))), inference(resolution, [status(thm)], [c_24, c_197])).
% 2.71/1.39  tff(c_209, plain, (![A_9]: (r2_hidden(A_9, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_206])).
% 2.71/1.39  tff(c_256, plain, (![A_133, B_134, C_135]: (r2_hidden(k1_mcart_1(A_133), B_134) | ~r2_hidden(A_133, k2_zfmisc_1(B_134, C_135)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.71/1.39  tff(c_259, plain, (r2_hidden(k1_mcart_1('#skF_9'), k2_tarski('#skF_10', '#skF_11'))), inference(resolution, [status(thm)], [c_76, c_256])).
% 2.71/1.39  tff(c_311, plain, (![C_146, A_147, B_148]: (k4_xboole_0(C_146, k2_tarski(A_147, B_148))=C_146 | r2_hidden(B_148, C_146) | r2_hidden(A_147, C_146))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.71/1.39  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.71/1.39  tff(c_482, plain, (![D_171, A_172, B_173, C_174]: (~r2_hidden(D_171, k2_tarski(A_172, B_173)) | ~r2_hidden(D_171, C_174) | r2_hidden(B_173, C_174) | r2_hidden(A_172, C_174))), inference(superposition, [status(thm), theory('equality')], [c_311, c_4])).
% 2.71/1.39  tff(c_502, plain, (![C_175]: (~r2_hidden(k1_mcart_1('#skF_9'), C_175) | r2_hidden('#skF_11', C_175) | r2_hidden('#skF_10', C_175))), inference(resolution, [status(thm)], [c_259, c_482])).
% 2.71/1.39  tff(c_526, plain, (r2_hidden('#skF_11', k1_tarski(k1_mcart_1('#skF_9'))) | r2_hidden('#skF_10', k1_tarski(k1_mcart_1('#skF_9')))), inference(resolution, [status(thm)], [c_209, c_502])).
% 2.71/1.39  tff(c_528, plain, (r2_hidden('#skF_10', k1_tarski(k1_mcart_1('#skF_9')))), inference(splitLeft, [status(thm)], [c_526])).
% 2.71/1.39  tff(c_72, plain, (![A_61, B_62]: (k1_mcart_1(k4_tarski(A_61, B_62))=A_61)), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.71/1.39  tff(c_357, plain, (![E_153, F_154, A_155, B_156]: (r2_hidden(k4_tarski(E_153, F_154), k2_zfmisc_1(A_155, B_156)) | ~r2_hidden(F_154, B_156) | ~r2_hidden(E_153, A_155))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.71/1.39  tff(c_70, plain, (![A_58, B_59, C_60]: (k1_mcart_1(A_58)=B_59 | ~r2_hidden(A_58, k2_zfmisc_1(k1_tarski(B_59), C_60)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.71/1.39  tff(c_365, plain, (![E_153, F_154, B_59, B_156]: (k1_mcart_1(k4_tarski(E_153, F_154))=B_59 | ~r2_hidden(F_154, B_156) | ~r2_hidden(E_153, k1_tarski(B_59)))), inference(resolution, [status(thm)], [c_357, c_70])).
% 2.71/1.39  tff(c_371, plain, (![E_153, B_59, F_154, B_156]: (E_153=B_59 | ~r2_hidden(F_154, B_156) | ~r2_hidden(E_153, k1_tarski(B_59)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_365])).
% 2.71/1.39  tff(c_400, plain, (![F_154, B_156]: (~r2_hidden(F_154, B_156))), inference(splitLeft, [status(thm)], [c_371])).
% 2.71/1.39  tff(c_418, plain, $false, inference(negUnitSimplification, [status(thm)], [c_400, c_259])).
% 2.71/1.39  tff(c_419, plain, (![E_153, B_59]: (E_153=B_59 | ~r2_hidden(E_153, k1_tarski(B_59)))), inference(splitRight, [status(thm)], [c_371])).
% 2.71/1.39  tff(c_542, plain, (k1_mcart_1('#skF_9')='#skF_10'), inference(resolution, [status(thm)], [c_528, c_419])).
% 2.71/1.39  tff(c_549, plain, $false, inference(negUnitSimplification, [status(thm)], [c_187, c_542])).
% 2.71/1.39  tff(c_550, plain, (r2_hidden('#skF_11', k1_tarski(k1_mcart_1('#skF_9')))), inference(splitRight, [status(thm)], [c_526])).
% 2.71/1.39  tff(c_556, plain, (k1_mcart_1('#skF_9')='#skF_11'), inference(resolution, [status(thm)], [c_550, c_419])).
% 2.71/1.39  tff(c_563, plain, $false, inference(negUnitSimplification, [status(thm)], [c_184, c_556])).
% 2.71/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.40  
% 2.71/1.40  Inference rules
% 2.71/1.40  ----------------------
% 2.71/1.40  #Ref     : 0
% 2.71/1.40  #Sup     : 98
% 2.71/1.40  #Fact    : 0
% 2.71/1.40  #Define  : 0
% 2.71/1.40  #Split   : 3
% 2.71/1.40  #Chain   : 0
% 2.71/1.40  #Close   : 0
% 2.71/1.40  
% 2.71/1.40  Ordering : KBO
% 2.71/1.40  
% 2.71/1.40  Simplification rules
% 2.71/1.40  ----------------------
% 2.71/1.40  #Subsume      : 17
% 2.71/1.40  #Demod        : 17
% 2.71/1.40  #Tautology    : 44
% 2.71/1.40  #SimpNegUnit  : 20
% 2.71/1.40  #BackRed      : 11
% 2.71/1.40  
% 2.71/1.40  #Partial instantiations: 0
% 2.71/1.40  #Strategies tried      : 1
% 2.71/1.40  
% 2.71/1.40  Timing (in seconds)
% 2.71/1.40  ----------------------
% 2.71/1.40  Preprocessing        : 0.33
% 2.71/1.40  Parsing              : 0.16
% 2.71/1.40  CNF conversion       : 0.03
% 2.71/1.40  Main loop            : 0.30
% 2.71/1.40  Inferencing          : 0.11
% 2.71/1.40  Reduction            : 0.09
% 2.71/1.40  Demodulation         : 0.07
% 2.71/1.40  BG Simplification    : 0.02
% 2.71/1.40  Subsumption          : 0.06
% 2.71/1.40  Abstraction          : 0.02
% 2.71/1.40  MUC search           : 0.00
% 2.71/1.40  Cooper               : 0.00
% 2.71/1.40  Total                : 0.66
% 2.71/1.40  Index Insertion      : 0.00
% 2.71/1.40  Index Deletion       : 0.00
% 2.71/1.40  Index Matching       : 0.00
% 2.71/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
