%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:29 EST 2020

% Result     : Theorem 3.84s
% Output     : CNFRefutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 227 expanded)
%              Number of leaves         :   28 (  87 expanded)
%              Depth                    :   13
%              Number of atoms          :   70 ( 305 expanded)
%              Number of equality atoms :   52 ( 257 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C] : k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A,B,C)))) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_mcart_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),k1_tarski(D)))
    <=> ( A = C
        & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_210,plain,(
    ! [A_73,B_74,C_75] : k2_zfmisc_1(k1_tarski(A_73),k2_tarski(B_74,C_75)) = k2_tarski(k4_tarski(A_73,B_74),k4_tarski(A_73,C_75)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_232,plain,(
    ! [A_73,C_75] : k2_zfmisc_1(k1_tarski(A_73),k2_tarski(C_75,C_75)) = k1_tarski(k4_tarski(A_73,C_75)) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_4])).

tff(c_269,plain,(
    ! [A_76,C_77] : k2_zfmisc_1(k1_tarski(A_76),k1_tarski(C_77)) = k1_tarski(k4_tarski(A_76,C_77)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_232])).

tff(c_30,plain,(
    ! [A_21,B_22] :
      ( k1_relat_1(k2_zfmisc_1(A_21,B_22)) = A_21
      | k1_xboole_0 = B_22
      | k1_xboole_0 = A_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_275,plain,(
    ! [A_76,C_77] :
      ( k1_relat_1(k1_tarski(k4_tarski(A_76,C_77))) = k1_tarski(A_76)
      | k1_tarski(C_77) = k1_xboole_0
      | k1_tarski(A_76) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_30])).

tff(c_34,plain,(
    ! [A_25,B_26,C_27] : k4_tarski(k4_tarski(A_25,B_26),C_27) = k3_mcart_1(A_25,B_26,C_27) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_476,plain,(
    ! [A_119,C_120] :
      ( k1_relat_1(k1_tarski(k4_tarski(A_119,C_120))) = k1_tarski(A_119)
      | k1_tarski(C_120) = k1_xboole_0
      | k1_tarski(A_119) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_30])).

tff(c_1329,plain,(
    ! [A_193,B_194,C_195] :
      ( k1_relat_1(k1_tarski(k3_mcart_1(A_193,B_194,C_195))) = k1_tarski(k4_tarski(A_193,B_194))
      | k1_tarski(C_195) = k1_xboole_0
      | k1_tarski(k4_tarski(A_193,B_194)) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_476])).

tff(c_36,plain,(
    k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1('#skF_1','#skF_2','#skF_3')))) != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1335,plain,
    ( k1_relat_1(k1_tarski(k4_tarski('#skF_1','#skF_2'))) != k1_tarski('#skF_1')
    | k1_tarski('#skF_3') = k1_xboole_0
    | k1_tarski(k4_tarski('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1329,c_36])).

tff(c_1345,plain,(
    k1_relat_1(k1_tarski(k4_tarski('#skF_1','#skF_2'))) != k1_tarski('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1335])).

tff(c_1349,plain,
    ( k1_tarski('#skF_2') = k1_xboole_0
    | k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_1345])).

tff(c_1350,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1349])).

tff(c_257,plain,(
    ! [A_73,C_75] : k2_zfmisc_1(k1_tarski(A_73),k1_tarski(C_75)) = k1_tarski(k4_tarski(A_73,C_75)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_232])).

tff(c_1383,plain,(
    ! [C_75] : k2_zfmisc_1(k1_xboole_0,k1_tarski(C_75)) = k1_tarski(k4_tarski('#skF_1',C_75)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1350,c_257])).

tff(c_1405,plain,(
    ! [C_196] : k1_tarski(k4_tarski('#skF_1',C_196)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1383])).

tff(c_154,plain,(
    ! [C_48,D_49] : r2_hidden(k4_tarski(C_48,D_49),k2_zfmisc_1(k1_tarski(C_48),k1_tarski(D_49))) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_32,plain,(
    ! [B_24,A_23] :
      ( ~ r1_tarski(B_24,A_23)
      | ~ r2_hidden(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_161,plain,(
    ! [C_48,D_49] : ~ r1_tarski(k2_zfmisc_1(k1_tarski(C_48),k1_tarski(D_49)),k4_tarski(C_48,D_49)) ),
    inference(resolution,[status(thm)],[c_154,c_32])).

tff(c_267,plain,(
    ! [C_48,D_49] : ~ r1_tarski(k1_tarski(k4_tarski(C_48,D_49)),k4_tarski(C_48,D_49)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_161])).

tff(c_1455,plain,(
    ! [C_196] : ~ r1_tarski(k1_xboole_0,k4_tarski('#skF_1',C_196)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1405,c_267])).

tff(c_1478,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1455])).

tff(c_1479,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1349])).

tff(c_1511,plain,(
    ! [C_75] : k2_zfmisc_1(k1_xboole_0,k1_tarski(C_75)) = k1_tarski(k4_tarski('#skF_2',C_75)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1479,c_257])).

tff(c_1533,plain,(
    ! [C_197] : k1_tarski(k4_tarski('#skF_2',C_197)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1511])).

tff(c_1583,plain,(
    ! [C_197] : ~ r1_tarski(k1_xboole_0,k4_tarski('#skF_2',C_197)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1533,c_267])).

tff(c_1606,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1583])).

tff(c_1607,plain,
    ( k1_tarski(k4_tarski('#skF_1','#skF_2')) = k1_xboole_0
    | k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1335])).

tff(c_1621,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1607])).

tff(c_1652,plain,(
    ! [C_75] : k2_zfmisc_1(k1_xboole_0,k1_tarski(C_75)) = k1_tarski(k4_tarski('#skF_3',C_75)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1621,c_257])).

tff(c_1674,plain,(
    ! [C_198] : k1_tarski(k4_tarski('#skF_3',C_198)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1652])).

tff(c_1724,plain,(
    ! [C_198] : ~ r1_tarski(k1_xboole_0,k4_tarski('#skF_3',C_198)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1674,c_267])).

tff(c_1747,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1724])).

tff(c_1748,plain,(
    k1_tarski(k4_tarski('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1607])).

tff(c_1799,plain,(
    ~ r1_tarski(k1_xboole_0,k4_tarski('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1748,c_267])).

tff(c_1818,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1799])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:07:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.84/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.84/1.72  
% 3.84/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.84/1.72  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.84/1.72  
% 3.84/1.72  %Foreground sorts:
% 3.84/1.72  
% 3.84/1.72  
% 3.84/1.72  %Background operators:
% 3.84/1.72  
% 3.84/1.72  
% 3.84/1.72  %Foreground operators:
% 3.84/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.84/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.84/1.72  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.84/1.72  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.84/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.84/1.72  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.84/1.72  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.84/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.84/1.72  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.84/1.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.84/1.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.84/1.72  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.84/1.72  tff('#skF_2', type, '#skF_2': $i).
% 3.84/1.72  tff('#skF_3', type, '#skF_3': $i).
% 3.84/1.72  tff('#skF_1', type, '#skF_1': $i).
% 3.84/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.84/1.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.84/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.84/1.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.84/1.72  
% 3.84/1.73  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.84/1.73  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.84/1.73  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.84/1.73  tff(f_51, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 3.84/1.73  tff(f_63, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 3.84/1.73  tff(f_70, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 3.84/1.73  tff(f_73, negated_conjecture, ~(![A, B, C]: (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A, B, C)))) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_mcart_1)).
% 3.84/1.73  tff(f_47, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), k1_tarski(D))) <=> ((A = C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_zfmisc_1)).
% 3.84/1.73  tff(f_68, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.84/1.73  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.84/1.73  tff(c_16, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.84/1.73  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.84/1.73  tff(c_210, plain, (![A_73, B_74, C_75]: (k2_zfmisc_1(k1_tarski(A_73), k2_tarski(B_74, C_75))=k2_tarski(k4_tarski(A_73, B_74), k4_tarski(A_73, C_75)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.84/1.73  tff(c_232, plain, (![A_73, C_75]: (k2_zfmisc_1(k1_tarski(A_73), k2_tarski(C_75, C_75))=k1_tarski(k4_tarski(A_73, C_75)))), inference(superposition, [status(thm), theory('equality')], [c_210, c_4])).
% 3.84/1.73  tff(c_269, plain, (![A_76, C_77]: (k2_zfmisc_1(k1_tarski(A_76), k1_tarski(C_77))=k1_tarski(k4_tarski(A_76, C_77)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_232])).
% 3.84/1.73  tff(c_30, plain, (![A_21, B_22]: (k1_relat_1(k2_zfmisc_1(A_21, B_22))=A_21 | k1_xboole_0=B_22 | k1_xboole_0=A_21)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.84/1.73  tff(c_275, plain, (![A_76, C_77]: (k1_relat_1(k1_tarski(k4_tarski(A_76, C_77)))=k1_tarski(A_76) | k1_tarski(C_77)=k1_xboole_0 | k1_tarski(A_76)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_269, c_30])).
% 3.84/1.73  tff(c_34, plain, (![A_25, B_26, C_27]: (k4_tarski(k4_tarski(A_25, B_26), C_27)=k3_mcart_1(A_25, B_26, C_27))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.84/1.73  tff(c_476, plain, (![A_119, C_120]: (k1_relat_1(k1_tarski(k4_tarski(A_119, C_120)))=k1_tarski(A_119) | k1_tarski(C_120)=k1_xboole_0 | k1_tarski(A_119)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_269, c_30])).
% 3.84/1.73  tff(c_1329, plain, (![A_193, B_194, C_195]: (k1_relat_1(k1_tarski(k3_mcart_1(A_193, B_194, C_195)))=k1_tarski(k4_tarski(A_193, B_194)) | k1_tarski(C_195)=k1_xboole_0 | k1_tarski(k4_tarski(A_193, B_194))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_34, c_476])).
% 3.84/1.73  tff(c_36, plain, (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'))))!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.84/1.73  tff(c_1335, plain, (k1_relat_1(k1_tarski(k4_tarski('#skF_1', '#skF_2')))!=k1_tarski('#skF_1') | k1_tarski('#skF_3')=k1_xboole_0 | k1_tarski(k4_tarski('#skF_1', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1329, c_36])).
% 3.84/1.73  tff(c_1345, plain, (k1_relat_1(k1_tarski(k4_tarski('#skF_1', '#skF_2')))!=k1_tarski('#skF_1')), inference(splitLeft, [status(thm)], [c_1335])).
% 3.84/1.73  tff(c_1349, plain, (k1_tarski('#skF_2')=k1_xboole_0 | k1_tarski('#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_275, c_1345])).
% 3.84/1.73  tff(c_1350, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1349])).
% 3.84/1.73  tff(c_257, plain, (![A_73, C_75]: (k2_zfmisc_1(k1_tarski(A_73), k1_tarski(C_75))=k1_tarski(k4_tarski(A_73, C_75)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_232])).
% 3.84/1.73  tff(c_1383, plain, (![C_75]: (k2_zfmisc_1(k1_xboole_0, k1_tarski(C_75))=k1_tarski(k4_tarski('#skF_1', C_75)))), inference(superposition, [status(thm), theory('equality')], [c_1350, c_257])).
% 3.84/1.73  tff(c_1405, plain, (![C_196]: (k1_tarski(k4_tarski('#skF_1', C_196))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1383])).
% 3.84/1.73  tff(c_154, plain, (![C_48, D_49]: (r2_hidden(k4_tarski(C_48, D_49), k2_zfmisc_1(k1_tarski(C_48), k1_tarski(D_49))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.84/1.73  tff(c_32, plain, (![B_24, A_23]: (~r1_tarski(B_24, A_23) | ~r2_hidden(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.84/1.73  tff(c_161, plain, (![C_48, D_49]: (~r1_tarski(k2_zfmisc_1(k1_tarski(C_48), k1_tarski(D_49)), k4_tarski(C_48, D_49)))), inference(resolution, [status(thm)], [c_154, c_32])).
% 3.84/1.73  tff(c_267, plain, (![C_48, D_49]: (~r1_tarski(k1_tarski(k4_tarski(C_48, D_49)), k4_tarski(C_48, D_49)))), inference(demodulation, [status(thm), theory('equality')], [c_257, c_161])).
% 3.84/1.73  tff(c_1455, plain, (![C_196]: (~r1_tarski(k1_xboole_0, k4_tarski('#skF_1', C_196)))), inference(superposition, [status(thm), theory('equality')], [c_1405, c_267])).
% 3.84/1.73  tff(c_1478, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_1455])).
% 3.84/1.73  tff(c_1479, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1349])).
% 3.84/1.73  tff(c_1511, plain, (![C_75]: (k2_zfmisc_1(k1_xboole_0, k1_tarski(C_75))=k1_tarski(k4_tarski('#skF_2', C_75)))), inference(superposition, [status(thm), theory('equality')], [c_1479, c_257])).
% 3.84/1.73  tff(c_1533, plain, (![C_197]: (k1_tarski(k4_tarski('#skF_2', C_197))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1511])).
% 3.84/1.73  tff(c_1583, plain, (![C_197]: (~r1_tarski(k1_xboole_0, k4_tarski('#skF_2', C_197)))), inference(superposition, [status(thm), theory('equality')], [c_1533, c_267])).
% 3.84/1.73  tff(c_1606, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_1583])).
% 3.84/1.73  tff(c_1607, plain, (k1_tarski(k4_tarski('#skF_1', '#skF_2'))=k1_xboole_0 | k1_tarski('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1335])).
% 3.84/1.73  tff(c_1621, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1607])).
% 3.84/1.73  tff(c_1652, plain, (![C_75]: (k2_zfmisc_1(k1_xboole_0, k1_tarski(C_75))=k1_tarski(k4_tarski('#skF_3', C_75)))), inference(superposition, [status(thm), theory('equality')], [c_1621, c_257])).
% 3.84/1.73  tff(c_1674, plain, (![C_198]: (k1_tarski(k4_tarski('#skF_3', C_198))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1652])).
% 3.84/1.73  tff(c_1724, plain, (![C_198]: (~r1_tarski(k1_xboole_0, k4_tarski('#skF_3', C_198)))), inference(superposition, [status(thm), theory('equality')], [c_1674, c_267])).
% 3.84/1.73  tff(c_1747, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_1724])).
% 3.84/1.73  tff(c_1748, plain, (k1_tarski(k4_tarski('#skF_1', '#skF_2'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_1607])).
% 3.84/1.73  tff(c_1799, plain, (~r1_tarski(k1_xboole_0, k4_tarski('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1748, c_267])).
% 3.84/1.73  tff(c_1818, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_1799])).
% 3.84/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.84/1.73  
% 3.84/1.73  Inference rules
% 3.84/1.73  ----------------------
% 3.84/1.73  #Ref     : 0
% 3.84/1.73  #Sup     : 453
% 3.84/1.73  #Fact    : 0
% 3.84/1.73  #Define  : 0
% 3.84/1.73  #Split   : 3
% 3.84/1.73  #Chain   : 0
% 3.84/1.73  #Close   : 0
% 3.84/1.73  
% 3.84/1.73  Ordering : KBO
% 3.84/1.73  
% 3.84/1.73  Simplification rules
% 3.84/1.73  ----------------------
% 3.84/1.73  #Subsume      : 61
% 3.84/1.73  #Demod        : 346
% 3.84/1.73  #Tautology    : 155
% 3.84/1.73  #SimpNegUnit  : 0
% 3.84/1.73  #BackRed      : 8
% 3.84/1.73  
% 3.84/1.73  #Partial instantiations: 0
% 3.84/1.73  #Strategies tried      : 1
% 3.84/1.73  
% 3.84/1.73  Timing (in seconds)
% 3.84/1.73  ----------------------
% 3.84/1.73  Preprocessing        : 0.31
% 3.84/1.73  Parsing              : 0.16
% 3.84/1.73  CNF conversion       : 0.02
% 3.84/1.73  Main loop            : 0.64
% 3.84/1.73  Inferencing          : 0.25
% 3.84/1.73  Reduction            : 0.24
% 3.84/1.73  Demodulation         : 0.19
% 3.84/1.73  BG Simplification    : 0.03
% 3.84/1.73  Subsumption          : 0.08
% 3.84/1.73  Abstraction          : 0.05
% 3.84/1.73  MUC search           : 0.00
% 3.84/1.73  Cooper               : 0.00
% 3.84/1.73  Total                : 0.98
% 3.84/1.73  Index Insertion      : 0.00
% 3.84/1.73  Index Deletion       : 0.00
% 3.84/1.73  Index Matching       : 0.00
% 3.84/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
