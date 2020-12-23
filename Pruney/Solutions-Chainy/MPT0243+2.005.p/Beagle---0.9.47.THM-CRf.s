%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:55 EST 2020

% Result     : Theorem 11.91s
% Output     : CNFRefutation 11.91s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 165 expanded)
%              Number of leaves         :   31 (  63 expanded)
%              Depth                    :    8
%              Number of atoms          :  112 ( 288 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_11 > #skF_7 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),C)
      <=> ( r2_hidden(A,C)
          & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_90,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_84,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_82,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_78,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | ~ r2_hidden('#skF_10','#skF_11')
    | ~ r2_hidden('#skF_9','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_350,plain,(
    ~ r2_hidden('#skF_9','#skF_11') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_72,plain,(
    ! [A_37,B_38] : r1_tarski(k1_tarski(A_37),k2_tarski(A_37,B_38)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_91,plain,(
    ! [A_51,B_52] :
      ( r2_hidden(A_51,B_52)
      | ~ r1_tarski(k1_tarski(A_51),B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_99,plain,(
    ! [A_37,B_38] : r2_hidden(A_37,k2_tarski(A_37,B_38)) ),
    inference(resolution,[status(thm)],[c_72,c_91])).

tff(c_82,plain,
    ( r2_hidden('#skF_7','#skF_8')
    | r1_tarski(k2_tarski('#skF_9','#skF_10'),'#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_112,plain,(
    r1_tarski(k2_tarski('#skF_9','#skF_10'),'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_36,plain,(
    ! [A_19,B_20] :
      ( k3_xboole_0(A_19,B_20) = A_19
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_125,plain,(
    k3_xboole_0(k2_tarski('#skF_9','#skF_10'),'#skF_11') = k2_tarski('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_112,c_36])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_571,plain,(
    ! [D_103] :
      ( r2_hidden(D_103,'#skF_11')
      | ~ r2_hidden(D_103,k2_tarski('#skF_9','#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_10])).

tff(c_583,plain,(
    r2_hidden('#skF_9','#skF_11') ),
    inference(resolution,[status(thm)],[c_99,c_571])).

tff(c_589,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_350,c_583])).

tff(c_590,plain,
    ( ~ r2_hidden('#skF_10','#skF_11')
    | r2_hidden('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_592,plain,(
    ~ r2_hidden('#skF_10','#skF_11') ),
    inference(splitLeft,[status(thm)],[c_590])).

tff(c_161,plain,(
    ! [A_64,B_65] : k1_enumset1(A_64,A_64,B_65) = k2_tarski(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_42,plain,(
    ! [E_30,A_24,B_25] : r2_hidden(E_30,k1_enumset1(A_24,B_25,E_30)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_167,plain,(
    ! [B_65,A_64] : r2_hidden(B_65,k2_tarski(A_64,B_65)) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_42])).

tff(c_802,plain,(
    ! [C_120,B_121,A_122] :
      ( r2_hidden(C_120,B_121)
      | ~ r2_hidden(C_120,A_122)
      | ~ r1_tarski(A_122,B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_844,plain,(
    ! [B_124,B_125,A_126] :
      ( r2_hidden(B_124,B_125)
      | ~ r1_tarski(k2_tarski(A_126,B_124),B_125) ) ),
    inference(resolution,[status(thm)],[c_167,c_802])).

tff(c_861,plain,(
    r2_hidden('#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_112,c_844])).

tff(c_872,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_592,c_861])).

tff(c_874,plain,(
    r2_hidden('#skF_10','#skF_11') ),
    inference(splitRight,[status(thm)],[c_590])).

tff(c_591,plain,(
    r2_hidden('#skF_9','#skF_11') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_76,plain,
    ( r2_hidden('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_10','#skF_11')
    | ~ r2_hidden('#skF_9','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_876,plain,
    ( r2_hidden('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_10','#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_591,c_76])).

tff(c_877,plain,(
    ~ r2_hidden('#skF_10','#skF_11') ),
    inference(splitLeft,[status(thm)],[c_876])).

tff(c_879,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_874,c_877])).

tff(c_880,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_876])).

tff(c_70,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(k1_tarski(A_35),B_36)
      | ~ r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_873,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_590])).

tff(c_64,plain,(
    ! [A_31,B_32] : k2_xboole_0(k1_tarski(A_31),k1_tarski(B_32)) = k2_tarski(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1460,plain,(
    ! [A_177,C_178,B_179] :
      ( r1_tarski(k2_xboole_0(A_177,C_178),B_179)
      | ~ r1_tarski(C_178,B_179)
      | ~ r1_tarski(A_177,B_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_17084,plain,(
    ! [A_18429,B_18430,B_18431] :
      ( r1_tarski(k2_tarski(A_18429,B_18430),B_18431)
      | ~ r1_tarski(k1_tarski(B_18430),B_18431)
      | ~ r1_tarski(k1_tarski(A_18429),B_18431) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_1460])).

tff(c_74,plain,
    ( ~ r1_tarski(k2_tarski('#skF_6','#skF_7'),'#skF_8')
    | ~ r2_hidden('#skF_10','#skF_11')
    | ~ r2_hidden('#skF_9','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1183,plain,(
    ~ r1_tarski(k2_tarski('#skF_6','#skF_7'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_591,c_874,c_74])).

tff(c_17145,plain,
    ( ~ r1_tarski(k1_tarski('#skF_7'),'#skF_8')
    | ~ r1_tarski(k1_tarski('#skF_6'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_17084,c_1183])).

tff(c_17422,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_17145])).

tff(c_17425,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_17422])).

tff(c_17429,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_873,c_17425])).

tff(c_17430,plain,(
    ~ r1_tarski(k1_tarski('#skF_7'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_17145])).

tff(c_17434,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_17430])).

tff(c_17438,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_880,c_17434])).

tff(c_17439,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_17440,plain,(
    ~ r1_tarski(k2_tarski('#skF_9','#skF_10'),'#skF_11') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_84,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | r1_tarski(k2_tarski('#skF_9','#skF_10'),'#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_17489,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_17440,c_84])).

tff(c_18090,plain,(
    ! [A_18982,C_18983,B_18984] :
      ( r1_tarski(k2_xboole_0(A_18982,C_18983),B_18984)
      | ~ r1_tarski(C_18983,B_18984)
      | ~ r1_tarski(A_18982,B_18984) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_30465,plain,(
    ! [A_34135,B_34136,B_34137] :
      ( r1_tarski(k2_tarski(A_34135,B_34136),B_34137)
      | ~ r1_tarski(k1_tarski(B_34136),B_34137)
      | ~ r1_tarski(k1_tarski(A_34135),B_34137) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_18090])).

tff(c_80,plain,
    ( ~ r1_tarski(k2_tarski('#skF_6','#skF_7'),'#skF_8')
    | r1_tarski(k2_tarski('#skF_9','#skF_10'),'#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_17823,plain,(
    ~ r1_tarski(k2_tarski('#skF_6','#skF_7'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_17440,c_80])).

tff(c_30527,plain,
    ( ~ r1_tarski(k1_tarski('#skF_7'),'#skF_8')
    | ~ r1_tarski(k1_tarski('#skF_6'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_30465,c_17823])).

tff(c_30533,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_30527])).

tff(c_30536,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_30533])).

tff(c_30540,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17489,c_30536])).

tff(c_30541,plain,(
    ~ r1_tarski(k1_tarski('#skF_7'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_30527])).

tff(c_30546,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_30541])).

tff(c_30550,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17439,c_30546])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:41:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.91/4.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.91/4.70  
% 11.91/4.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.91/4.70  %$ r2_hidden > r1_tarski > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_11 > #skF_7 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_3 > #skF_1
% 11.91/4.70  
% 11.91/4.70  %Foreground sorts:
% 11.91/4.70  
% 11.91/4.70  
% 11.91/4.70  %Background operators:
% 11.91/4.70  
% 11.91/4.70  
% 11.91/4.70  %Foreground operators:
% 11.91/4.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.91/4.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.91/4.70  tff('#skF_11', type, '#skF_11': $i).
% 11.91/4.70  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.91/4.70  tff('#skF_7', type, '#skF_7': $i).
% 11.91/4.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.91/4.70  tff('#skF_10', type, '#skF_10': $i).
% 11.91/4.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.91/4.70  tff('#skF_6', type, '#skF_6': $i).
% 11.91/4.70  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.91/4.70  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.91/4.70  tff('#skF_9', type, '#skF_9': $i).
% 11.91/4.70  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 11.91/4.70  tff('#skF_8', type, '#skF_8': $i).
% 11.91/4.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.91/4.70  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 11.91/4.70  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 11.91/4.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.91/4.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.91/4.70  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.91/4.70  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.91/4.70  
% 11.91/4.72  tff(f_97, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 11.91/4.72  tff(f_90, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 11.91/4.72  tff(f_88, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 11.91/4.72  tff(f_59, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 11.91/4.72  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 11.91/4.72  tff(f_84, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 11.91/4.72  tff(f_80, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 11.91/4.72  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 11.91/4.72  tff(f_82, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 11.91/4.72  tff(f_65, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 11.91/4.72  tff(c_78, plain, (r2_hidden('#skF_6', '#skF_8') | ~r2_hidden('#skF_10', '#skF_11') | ~r2_hidden('#skF_9', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.91/4.72  tff(c_350, plain, (~r2_hidden('#skF_9', '#skF_11')), inference(splitLeft, [status(thm)], [c_78])).
% 11.91/4.72  tff(c_72, plain, (![A_37, B_38]: (r1_tarski(k1_tarski(A_37), k2_tarski(A_37, B_38)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.91/4.72  tff(c_91, plain, (![A_51, B_52]: (r2_hidden(A_51, B_52) | ~r1_tarski(k1_tarski(A_51), B_52))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.91/4.72  tff(c_99, plain, (![A_37, B_38]: (r2_hidden(A_37, k2_tarski(A_37, B_38)))), inference(resolution, [status(thm)], [c_72, c_91])).
% 11.91/4.72  tff(c_82, plain, (r2_hidden('#skF_7', '#skF_8') | r1_tarski(k2_tarski('#skF_9', '#skF_10'), '#skF_11')), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.91/4.72  tff(c_112, plain, (r1_tarski(k2_tarski('#skF_9', '#skF_10'), '#skF_11')), inference(splitLeft, [status(thm)], [c_82])).
% 11.91/4.72  tff(c_36, plain, (![A_19, B_20]: (k3_xboole_0(A_19, B_20)=A_19 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.91/4.72  tff(c_125, plain, (k3_xboole_0(k2_tarski('#skF_9', '#skF_10'), '#skF_11')=k2_tarski('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_112, c_36])).
% 11.91/4.72  tff(c_10, plain, (![D_11, B_7, A_6]: (r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.91/4.72  tff(c_571, plain, (![D_103]: (r2_hidden(D_103, '#skF_11') | ~r2_hidden(D_103, k2_tarski('#skF_9', '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_125, c_10])).
% 11.91/4.72  tff(c_583, plain, (r2_hidden('#skF_9', '#skF_11')), inference(resolution, [status(thm)], [c_99, c_571])).
% 11.91/4.72  tff(c_589, plain, $false, inference(negUnitSimplification, [status(thm)], [c_350, c_583])).
% 11.91/4.72  tff(c_590, plain, (~r2_hidden('#skF_10', '#skF_11') | r2_hidden('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_78])).
% 11.91/4.72  tff(c_592, plain, (~r2_hidden('#skF_10', '#skF_11')), inference(splitLeft, [status(thm)], [c_590])).
% 11.91/4.72  tff(c_161, plain, (![A_64, B_65]: (k1_enumset1(A_64, A_64, B_65)=k2_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_84])).
% 11.91/4.72  tff(c_42, plain, (![E_30, A_24, B_25]: (r2_hidden(E_30, k1_enumset1(A_24, B_25, E_30)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.91/4.72  tff(c_167, plain, (![B_65, A_64]: (r2_hidden(B_65, k2_tarski(A_64, B_65)))), inference(superposition, [status(thm), theory('equality')], [c_161, c_42])).
% 11.91/4.72  tff(c_802, plain, (![C_120, B_121, A_122]: (r2_hidden(C_120, B_121) | ~r2_hidden(C_120, A_122) | ~r1_tarski(A_122, B_121))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.91/4.72  tff(c_844, plain, (![B_124, B_125, A_126]: (r2_hidden(B_124, B_125) | ~r1_tarski(k2_tarski(A_126, B_124), B_125))), inference(resolution, [status(thm)], [c_167, c_802])).
% 11.91/4.72  tff(c_861, plain, (r2_hidden('#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_112, c_844])).
% 11.91/4.72  tff(c_872, plain, $false, inference(negUnitSimplification, [status(thm)], [c_592, c_861])).
% 11.91/4.72  tff(c_874, plain, (r2_hidden('#skF_10', '#skF_11')), inference(splitRight, [status(thm)], [c_590])).
% 11.91/4.72  tff(c_591, plain, (r2_hidden('#skF_9', '#skF_11')), inference(splitRight, [status(thm)], [c_78])).
% 11.91/4.72  tff(c_76, plain, (r2_hidden('#skF_7', '#skF_8') | ~r2_hidden('#skF_10', '#skF_11') | ~r2_hidden('#skF_9', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.91/4.72  tff(c_876, plain, (r2_hidden('#skF_7', '#skF_8') | ~r2_hidden('#skF_10', '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_591, c_76])).
% 11.91/4.72  tff(c_877, plain, (~r2_hidden('#skF_10', '#skF_11')), inference(splitLeft, [status(thm)], [c_876])).
% 11.91/4.72  tff(c_879, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_874, c_877])).
% 11.91/4.72  tff(c_880, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_876])).
% 11.91/4.72  tff(c_70, plain, (![A_35, B_36]: (r1_tarski(k1_tarski(A_35), B_36) | ~r2_hidden(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.91/4.72  tff(c_873, plain, (r2_hidden('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_590])).
% 11.91/4.72  tff(c_64, plain, (![A_31, B_32]: (k2_xboole_0(k1_tarski(A_31), k1_tarski(B_32))=k2_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.91/4.72  tff(c_1460, plain, (![A_177, C_178, B_179]: (r1_tarski(k2_xboole_0(A_177, C_178), B_179) | ~r1_tarski(C_178, B_179) | ~r1_tarski(A_177, B_179))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.91/4.72  tff(c_17084, plain, (![A_18429, B_18430, B_18431]: (r1_tarski(k2_tarski(A_18429, B_18430), B_18431) | ~r1_tarski(k1_tarski(B_18430), B_18431) | ~r1_tarski(k1_tarski(A_18429), B_18431))), inference(superposition, [status(thm), theory('equality')], [c_64, c_1460])).
% 11.91/4.72  tff(c_74, plain, (~r1_tarski(k2_tarski('#skF_6', '#skF_7'), '#skF_8') | ~r2_hidden('#skF_10', '#skF_11') | ~r2_hidden('#skF_9', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.91/4.72  tff(c_1183, plain, (~r1_tarski(k2_tarski('#skF_6', '#skF_7'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_591, c_874, c_74])).
% 11.91/4.72  tff(c_17145, plain, (~r1_tarski(k1_tarski('#skF_7'), '#skF_8') | ~r1_tarski(k1_tarski('#skF_6'), '#skF_8')), inference(resolution, [status(thm)], [c_17084, c_1183])).
% 11.91/4.72  tff(c_17422, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_8')), inference(splitLeft, [status(thm)], [c_17145])).
% 11.91/4.72  tff(c_17425, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_70, c_17422])).
% 11.91/4.72  tff(c_17429, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_873, c_17425])).
% 11.91/4.72  tff(c_17430, plain, (~r1_tarski(k1_tarski('#skF_7'), '#skF_8')), inference(splitRight, [status(thm)], [c_17145])).
% 11.91/4.72  tff(c_17434, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_70, c_17430])).
% 11.91/4.72  tff(c_17438, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_880, c_17434])).
% 11.91/4.72  tff(c_17439, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_82])).
% 11.91/4.72  tff(c_17440, plain, (~r1_tarski(k2_tarski('#skF_9', '#skF_10'), '#skF_11')), inference(splitRight, [status(thm)], [c_82])).
% 11.91/4.72  tff(c_84, plain, (r2_hidden('#skF_6', '#skF_8') | r1_tarski(k2_tarski('#skF_9', '#skF_10'), '#skF_11')), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.91/4.72  tff(c_17489, plain, (r2_hidden('#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_17440, c_84])).
% 11.91/4.72  tff(c_18090, plain, (![A_18982, C_18983, B_18984]: (r1_tarski(k2_xboole_0(A_18982, C_18983), B_18984) | ~r1_tarski(C_18983, B_18984) | ~r1_tarski(A_18982, B_18984))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.91/4.72  tff(c_30465, plain, (![A_34135, B_34136, B_34137]: (r1_tarski(k2_tarski(A_34135, B_34136), B_34137) | ~r1_tarski(k1_tarski(B_34136), B_34137) | ~r1_tarski(k1_tarski(A_34135), B_34137))), inference(superposition, [status(thm), theory('equality')], [c_64, c_18090])).
% 11.91/4.72  tff(c_80, plain, (~r1_tarski(k2_tarski('#skF_6', '#skF_7'), '#skF_8') | r1_tarski(k2_tarski('#skF_9', '#skF_10'), '#skF_11')), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.91/4.72  tff(c_17823, plain, (~r1_tarski(k2_tarski('#skF_6', '#skF_7'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_17440, c_80])).
% 11.91/4.72  tff(c_30527, plain, (~r1_tarski(k1_tarski('#skF_7'), '#skF_8') | ~r1_tarski(k1_tarski('#skF_6'), '#skF_8')), inference(resolution, [status(thm)], [c_30465, c_17823])).
% 11.91/4.72  tff(c_30533, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_8')), inference(splitLeft, [status(thm)], [c_30527])).
% 11.91/4.72  tff(c_30536, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_70, c_30533])).
% 11.91/4.72  tff(c_30540, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17489, c_30536])).
% 11.91/4.72  tff(c_30541, plain, (~r1_tarski(k1_tarski('#skF_7'), '#skF_8')), inference(splitRight, [status(thm)], [c_30527])).
% 11.91/4.72  tff(c_30546, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_70, c_30541])).
% 11.91/4.72  tff(c_30550, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17439, c_30546])).
% 11.91/4.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.91/4.72  
% 11.91/4.72  Inference rules
% 11.91/4.72  ----------------------
% 11.91/4.72  #Ref     : 0
% 11.91/4.72  #Sup     : 6322
% 11.91/4.72  #Fact    : 36
% 11.91/4.72  #Define  : 0
% 11.91/4.72  #Split   : 21
% 11.91/4.72  #Chain   : 0
% 11.91/4.72  #Close   : 0
% 11.91/4.72  
% 11.91/4.72  Ordering : KBO
% 11.91/4.72  
% 11.91/4.72  Simplification rules
% 11.91/4.72  ----------------------
% 11.91/4.72  #Subsume      : 1461
% 11.91/4.72  #Demod        : 2222
% 11.91/4.72  #Tautology    : 2229
% 11.91/4.72  #SimpNegUnit  : 4
% 11.91/4.72  #BackRed      : 0
% 11.91/4.72  
% 11.91/4.72  #Partial instantiations: 20496
% 11.91/4.72  #Strategies tried      : 1
% 11.91/4.72  
% 11.91/4.72  Timing (in seconds)
% 11.91/4.72  ----------------------
% 11.91/4.72  Preprocessing        : 0.35
% 11.91/4.72  Parsing              : 0.18
% 11.91/4.72  CNF conversion       : 0.03
% 11.91/4.72  Main loop            : 3.55
% 11.91/4.72  Inferencing          : 1.28
% 11.91/4.72  Reduction            : 1.16
% 11.91/4.72  Demodulation         : 0.90
% 11.91/4.72  BG Simplification    : 0.12
% 11.91/4.72  Subsumption          : 0.80
% 11.91/4.72  Abstraction          : 0.15
% 11.91/4.72  MUC search           : 0.00
% 11.91/4.72  Cooper               : 0.00
% 11.91/4.72  Total                : 3.93
% 11.91/4.72  Index Insertion      : 0.00
% 11.91/4.72  Index Deletion       : 0.00
% 11.91/4.72  Index Matching       : 0.00
% 11.91/4.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
