%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:00 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.89s
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
        ( r2_hidden(A,k2_zfmisc_1(B,k2_tarski(C,D)))
       => ( r2_hidden(k1_mcart_1(A),B)
          & ( k2_mcart_1(A) = C
            | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_mcart_1)).

tff(f_75,axiom,(
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

tff(f_69,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_63,axiom,(
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

tff(f_85,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

tff(c_60,plain,
    ( k2_mcart_1('#skF_3') != '#skF_6'
    | ~ r2_hidden(k1_mcart_1('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_101,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_58,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1('#skF_4',k2_tarski('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_155,plain,(
    ! [A_65,B_66,C_67] :
      ( r2_hidden(k1_mcart_1(A_65),B_66)
      | ~ r2_hidden(A_65,k2_zfmisc_1(B_66,C_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_157,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_155])).

tff(c_161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_157])).

tff(c_162,plain,(
    k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_163,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_62,plain,
    ( k2_mcart_1('#skF_3') != '#skF_5'
    | ~ r2_hidden(k1_mcart_1('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_165,plain,(
    k2_mcart_1('#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_62])).

tff(c_26,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_174,plain,(
    ! [B_73,C_74,A_75] :
      ( r2_hidden(B_73,C_74)
      | ~ r1_tarski(k2_tarski(A_75,B_73),C_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_183,plain,(
    ! [B_76,A_77] : r2_hidden(B_76,k2_tarski(A_77,B_76)) ),
    inference(resolution,[status(thm)],[c_24,c_174])).

tff(c_186,plain,(
    ! [A_9] : r2_hidden(A_9,k1_tarski(A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_183])).

tff(c_224,plain,(
    ! [A_95,C_96,B_97] :
      ( r2_hidden(k2_mcart_1(A_95),C_96)
      | ~ r2_hidden(A_95,k2_zfmisc_1(B_97,C_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_227,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),k2_tarski('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_58,c_224])).

tff(c_282,plain,(
    ! [C_119,A_120,B_121] :
      ( k4_xboole_0(C_119,k2_tarski(A_120,B_121)) = C_119
      | r2_hidden(B_121,C_119)
      | r2_hidden(A_120,C_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_388,plain,(
    ! [D_138,A_139,B_140,C_141] :
      ( ~ r2_hidden(D_138,k2_tarski(A_139,B_140))
      | ~ r2_hidden(D_138,C_141)
      | r2_hidden(B_140,C_141)
      | r2_hidden(A_139,C_141) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_4])).

tff(c_526,plain,(
    ! [C_147] :
      ( ~ r2_hidden(k2_mcart_1('#skF_3'),C_147)
      | r2_hidden('#skF_6',C_147)
      | r2_hidden('#skF_5',C_147) ) ),
    inference(resolution,[status(thm)],[c_227,c_388])).

tff(c_550,plain,
    ( r2_hidden('#skF_6',k1_tarski(k2_mcart_1('#skF_3')))
    | r2_hidden('#skF_5',k1_tarski(k2_mcart_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_186,c_526])).

tff(c_552,plain,(
    r2_hidden('#skF_5',k1_tarski(k2_mcart_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_550])).

tff(c_54,plain,(
    ! [A_31,B_32] : k1_mcart_1(k4_tarski(A_31,B_32)) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_328,plain,(
    ! [A_126,B_127,C_128,D_129] :
      ( r2_hidden(k4_tarski(A_126,B_127),k2_zfmisc_1(C_128,D_129))
      | ~ r2_hidden(B_127,D_129)
      | ~ r2_hidden(A_126,C_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_52,plain,(
    ! [A_28,B_29,C_30] :
      ( k1_mcart_1(A_28) = B_29
      | ~ r2_hidden(A_28,k2_zfmisc_1(k1_tarski(B_29),C_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_338,plain,(
    ! [A_126,B_127,B_29,D_129] :
      ( k1_mcart_1(k4_tarski(A_126,B_127)) = B_29
      | ~ r2_hidden(B_127,D_129)
      | ~ r2_hidden(A_126,k1_tarski(B_29)) ) ),
    inference(resolution,[status(thm)],[c_328,c_52])).

tff(c_346,plain,(
    ! [B_29,A_126,B_127,D_129] :
      ( B_29 = A_126
      | ~ r2_hidden(B_127,D_129)
      | ~ r2_hidden(A_126,k1_tarski(B_29)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_338])).

tff(c_356,plain,(
    ! [B_127,D_129] : ~ r2_hidden(B_127,D_129) ),
    inference(splitLeft,[status(thm)],[c_346])).

tff(c_376,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_356,c_227])).

tff(c_377,plain,(
    ! [B_29,A_126] :
      ( B_29 = A_126
      | ~ r2_hidden(A_126,k1_tarski(B_29)) ) ),
    inference(splitRight,[status(thm)],[c_346])).

tff(c_566,plain,(
    k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_552,c_377])).

tff(c_573,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_566])).

tff(c_574,plain,(
    r2_hidden('#skF_6',k1_tarski(k2_mcart_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_550])).

tff(c_580,plain,(
    k2_mcart_1('#skF_3') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_574,c_377])).

tff(c_587,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_580])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:52:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.44  
% 2.75/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.44  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 2.75/1.44  
% 2.75/1.44  %Foreground sorts:
% 2.75/1.44  
% 2.75/1.44  
% 2.75/1.44  %Background operators:
% 2.75/1.44  
% 2.75/1.44  
% 2.75/1.44  %Foreground operators:
% 2.75/1.44  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.75/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.75/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.75/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.75/1.44  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.75/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.75/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.75/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.75/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.75/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.75/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.75/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.75/1.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.75/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.44  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.75/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.75/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.75/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.44  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.75/1.44  
% 2.89/1.46  tff(f_94, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(B, k2_tarski(C, D))) => (r2_hidden(k1_mcart_1(A), B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_mcart_1)).
% 2.89/1.46  tff(f_75, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.89/1.46  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.89/1.46  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.89/1.46  tff(f_69, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.89/1.46  tff(f_63, axiom, (![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 2.89/1.46  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.89/1.46  tff(f_85, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.89/1.46  tff(f_53, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.89/1.46  tff(f_81, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_mcart_1)).
% 2.89/1.46  tff(c_60, plain, (k2_mcart_1('#skF_3')!='#skF_6' | ~r2_hidden(k1_mcart_1('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.89/1.46  tff(c_101, plain, (~r2_hidden(k1_mcart_1('#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_60])).
% 2.89/1.46  tff(c_58, plain, (r2_hidden('#skF_3', k2_zfmisc_1('#skF_4', k2_tarski('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.89/1.46  tff(c_155, plain, (![A_65, B_66, C_67]: (r2_hidden(k1_mcart_1(A_65), B_66) | ~r2_hidden(A_65, k2_zfmisc_1(B_66, C_67)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.89/1.46  tff(c_157, plain, (r2_hidden(k1_mcart_1('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_58, c_155])).
% 2.89/1.46  tff(c_161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_101, c_157])).
% 2.89/1.46  tff(c_162, plain, (k2_mcart_1('#skF_3')!='#skF_6'), inference(splitRight, [status(thm)], [c_60])).
% 2.89/1.46  tff(c_163, plain, (r2_hidden(k1_mcart_1('#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_60])).
% 2.89/1.46  tff(c_62, plain, (k2_mcart_1('#skF_3')!='#skF_5' | ~r2_hidden(k1_mcart_1('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.89/1.46  tff(c_165, plain, (k2_mcart_1('#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_163, c_62])).
% 2.89/1.46  tff(c_26, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.89/1.46  tff(c_24, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.89/1.46  tff(c_174, plain, (![B_73, C_74, A_75]: (r2_hidden(B_73, C_74) | ~r1_tarski(k2_tarski(A_75, B_73), C_74))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.89/1.46  tff(c_183, plain, (![B_76, A_77]: (r2_hidden(B_76, k2_tarski(A_77, B_76)))), inference(resolution, [status(thm)], [c_24, c_174])).
% 2.89/1.46  tff(c_186, plain, (![A_9]: (r2_hidden(A_9, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_183])).
% 2.89/1.46  tff(c_224, plain, (![A_95, C_96, B_97]: (r2_hidden(k2_mcart_1(A_95), C_96) | ~r2_hidden(A_95, k2_zfmisc_1(B_97, C_96)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.89/1.46  tff(c_227, plain, (r2_hidden(k2_mcart_1('#skF_3'), k2_tarski('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_58, c_224])).
% 2.89/1.46  tff(c_282, plain, (![C_119, A_120, B_121]: (k4_xboole_0(C_119, k2_tarski(A_120, B_121))=C_119 | r2_hidden(B_121, C_119) | r2_hidden(A_120, C_119))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.89/1.46  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.89/1.46  tff(c_388, plain, (![D_138, A_139, B_140, C_141]: (~r2_hidden(D_138, k2_tarski(A_139, B_140)) | ~r2_hidden(D_138, C_141) | r2_hidden(B_140, C_141) | r2_hidden(A_139, C_141))), inference(superposition, [status(thm), theory('equality')], [c_282, c_4])).
% 2.89/1.46  tff(c_526, plain, (![C_147]: (~r2_hidden(k2_mcart_1('#skF_3'), C_147) | r2_hidden('#skF_6', C_147) | r2_hidden('#skF_5', C_147))), inference(resolution, [status(thm)], [c_227, c_388])).
% 2.89/1.46  tff(c_550, plain, (r2_hidden('#skF_6', k1_tarski(k2_mcart_1('#skF_3'))) | r2_hidden('#skF_5', k1_tarski(k2_mcart_1('#skF_3')))), inference(resolution, [status(thm)], [c_186, c_526])).
% 2.89/1.46  tff(c_552, plain, (r2_hidden('#skF_5', k1_tarski(k2_mcart_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_550])).
% 2.89/1.46  tff(c_54, plain, (![A_31, B_32]: (k1_mcart_1(k4_tarski(A_31, B_32))=A_31)), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.89/1.46  tff(c_328, plain, (![A_126, B_127, C_128, D_129]: (r2_hidden(k4_tarski(A_126, B_127), k2_zfmisc_1(C_128, D_129)) | ~r2_hidden(B_127, D_129) | ~r2_hidden(A_126, C_128))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.89/1.46  tff(c_52, plain, (![A_28, B_29, C_30]: (k1_mcart_1(A_28)=B_29 | ~r2_hidden(A_28, k2_zfmisc_1(k1_tarski(B_29), C_30)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.89/1.46  tff(c_338, plain, (![A_126, B_127, B_29, D_129]: (k1_mcart_1(k4_tarski(A_126, B_127))=B_29 | ~r2_hidden(B_127, D_129) | ~r2_hidden(A_126, k1_tarski(B_29)))), inference(resolution, [status(thm)], [c_328, c_52])).
% 2.89/1.46  tff(c_346, plain, (![B_29, A_126, B_127, D_129]: (B_29=A_126 | ~r2_hidden(B_127, D_129) | ~r2_hidden(A_126, k1_tarski(B_29)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_338])).
% 2.89/1.46  tff(c_356, plain, (![B_127, D_129]: (~r2_hidden(B_127, D_129))), inference(splitLeft, [status(thm)], [c_346])).
% 2.89/1.46  tff(c_376, plain, $false, inference(negUnitSimplification, [status(thm)], [c_356, c_227])).
% 2.89/1.46  tff(c_377, plain, (![B_29, A_126]: (B_29=A_126 | ~r2_hidden(A_126, k1_tarski(B_29)))), inference(splitRight, [status(thm)], [c_346])).
% 2.89/1.46  tff(c_566, plain, (k2_mcart_1('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_552, c_377])).
% 2.89/1.46  tff(c_573, plain, $false, inference(negUnitSimplification, [status(thm)], [c_165, c_566])).
% 2.89/1.46  tff(c_574, plain, (r2_hidden('#skF_6', k1_tarski(k2_mcart_1('#skF_3')))), inference(splitRight, [status(thm)], [c_550])).
% 2.89/1.46  tff(c_580, plain, (k2_mcart_1('#skF_3')='#skF_6'), inference(resolution, [status(thm)], [c_574, c_377])).
% 2.89/1.46  tff(c_587, plain, $false, inference(negUnitSimplification, [status(thm)], [c_162, c_580])).
% 2.89/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.46  
% 2.89/1.46  Inference rules
% 2.89/1.46  ----------------------
% 2.89/1.46  #Ref     : 0
% 2.89/1.46  #Sup     : 107
% 2.89/1.46  #Fact    : 0
% 2.89/1.46  #Define  : 0
% 2.89/1.46  #Split   : 3
% 2.89/1.46  #Chain   : 0
% 2.89/1.46  #Close   : 0
% 2.89/1.46  
% 2.89/1.46  Ordering : KBO
% 2.89/1.46  
% 2.89/1.46  Simplification rules
% 2.89/1.46  ----------------------
% 2.89/1.46  #Subsume      : 19
% 2.89/1.46  #Demod        : 17
% 2.89/1.46  #Tautology    : 44
% 2.89/1.46  #SimpNegUnit  : 22
% 2.89/1.46  #BackRed      : 11
% 2.89/1.46  
% 2.89/1.46  #Partial instantiations: 0
% 2.89/1.46  #Strategies tried      : 1
% 2.89/1.46  
% 2.89/1.46  Timing (in seconds)
% 2.89/1.46  ----------------------
% 2.89/1.46  Preprocessing        : 0.31
% 2.89/1.46  Parsing              : 0.16
% 2.89/1.46  CNF conversion       : 0.02
% 2.89/1.46  Main loop            : 0.32
% 2.89/1.46  Inferencing          : 0.12
% 2.89/1.46  Reduction            : 0.09
% 2.89/1.46  Demodulation         : 0.06
% 2.89/1.46  BG Simplification    : 0.02
% 2.89/1.46  Subsumption          : 0.06
% 2.89/1.46  Abstraction          : 0.02
% 2.89/1.46  MUC search           : 0.00
% 2.89/1.46  Cooper               : 0.00
% 2.89/1.46  Total                : 0.66
% 2.89/1.46  Index Insertion      : 0.00
% 2.89/1.46  Index Deletion       : 0.00
% 2.89/1.46  Index Matching       : 0.00
% 2.89/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
