%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:00 EST 2020

% Result     : Theorem 5.60s
% Output     : CNFRefutation 5.76s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 105 expanded)
%              Number of leaves         :   36 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :   91 ( 143 expanded)
%              Number of equality atoms :   36 (  55 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_107,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_88,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_98,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_69,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_71,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_70,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_87,plain,(
    ! [A_53] : k2_tarski(A_53,A_53) = k1_tarski(A_53) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_40,plain,(
    ! [D_36,B_32] : r2_hidden(D_36,k2_tarski(D_36,B_32)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_93,plain,(
    ! [A_53] : r2_hidden(A_53,k1_tarski(A_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_40])).

tff(c_72,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_5'),k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1496,plain,(
    ! [B_133,A_134] :
      ( k1_tarski(B_133) = A_134
      | k1_xboole_0 = A_134
      | ~ r1_tarski(A_134,k1_tarski(B_133)) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1518,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_7')
    | k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_72,c_1496])).

tff(c_1525,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1518])).

tff(c_239,plain,(
    ! [A_70,B_71] :
      ( r1_xboole_0(A_70,B_71)
      | k3_xboole_0(A_70,B_71) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( r1_xboole_0(B_8,A_7)
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_249,plain,(
    ! [B_71,A_70] :
      ( r1_xboole_0(B_71,A_70)
      | k3_xboole_0(A_70,B_71) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_239,c_10])).

tff(c_68,plain,(
    r1_xboole_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_212,plain,(
    ! [A_68,B_69] :
      ( k3_xboole_0(A_68,B_69) = k1_xboole_0
      | ~ r1_xboole_0(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_227,plain,(
    k3_xboole_0('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_68,c_212])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2209,plain,(
    ! [A_154,B_155,C_156] :
      ( k3_xboole_0(A_154,k2_xboole_0(B_155,C_156)) = k3_xboole_0(A_154,C_156)
      | ~ r1_xboole_0(A_154,B_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_66,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_247,plain,(
    k3_xboole_0(k2_xboole_0('#skF_4','#skF_6'),'#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_239,c_66])).

tff(c_251,plain,(
    k3_xboole_0('#skF_5',k2_xboole_0('#skF_4','#skF_6')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_247])).

tff(c_2285,plain,
    ( k3_xboole_0('#skF_5','#skF_6') != k1_xboole_0
    | ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2209,c_251])).

tff(c_2353,plain,(
    ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_4,c_2285])).

tff(c_2379,plain,(
    k3_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_249,c_2353])).

tff(c_2390,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1525,c_2379])).

tff(c_2391,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_1518])).

tff(c_28,plain,(
    ! [A_24] : k4_xboole_0(A_24,k1_xboole_0) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_30,plain,(
    ! [A_25] : r1_xboole_0(A_25,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_228,plain,(
    ! [A_25] : k3_xboole_0(A_25,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_212])).

tff(c_414,plain,(
    ! [A_83,B_84] : k5_xboole_0(A_83,k3_xboole_0(A_83,B_84)) = k4_xboole_0(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_429,plain,(
    ! [A_25] : k5_xboole_0(A_25,k1_xboole_0) = k4_xboole_0(A_25,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_414])).

tff(c_441,plain,(
    ! [A_25] : k5_xboole_0(A_25,k1_xboole_0) = A_25 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_429])).

tff(c_138,plain,(
    ! [B_59,A_60] :
      ( r1_xboole_0(B_59,A_60)
      | ~ r1_xboole_0(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_143,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_138])).

tff(c_226,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_143,c_212])).

tff(c_426,plain,(
    k5_xboole_0('#skF_5',k1_xboole_0) = k4_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_414])).

tff(c_563,plain,(
    k4_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_441,c_426])).

tff(c_26,plain,(
    ! [A_22,B_23] : r1_tarski(k3_xboole_0(A_22,B_23),A_22) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_357,plain,(
    ! [A_75,C_76,B_77] :
      ( r1_xboole_0(A_75,C_76)
      | ~ r1_tarski(A_75,k4_xboole_0(B_77,C_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_376,plain,(
    ! [B_77,C_76,B_23] : r1_xboole_0(k3_xboole_0(k4_xboole_0(B_77,C_76),B_23),C_76) ),
    inference(resolution,[status(thm)],[c_26,c_357])).

tff(c_574,plain,(
    ! [B_92] : r1_xboole_0(k3_xboole_0('#skF_5',B_92),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_563,c_376])).

tff(c_588,plain,(
    ! [B_4] : r1_xboole_0(k3_xboole_0(B_4,'#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_574])).

tff(c_2402,plain,(
    r1_xboole_0(k1_tarski('#skF_7'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2391,c_588])).

tff(c_12,plain,(
    ! [A_9,B_10,C_13] :
      ( ~ r1_xboole_0(A_9,B_10)
      | ~ r2_hidden(C_13,B_10)
      | ~ r2_hidden(C_13,A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5436,plain,(
    ! [C_6577] :
      ( ~ r2_hidden(C_6577,'#skF_6')
      | ~ r2_hidden(C_6577,k1_tarski('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_2402,c_12])).

tff(c_5448,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_93,c_5436])).

tff(c_5454,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_5448])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:52:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.60/2.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.76/2.15  
% 5.76/2.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.76/2.15  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 5.76/2.15  
% 5.76/2.15  %Foreground sorts:
% 5.76/2.15  
% 5.76/2.15  
% 5.76/2.15  %Background operators:
% 5.76/2.15  
% 5.76/2.15  
% 5.76/2.15  %Foreground operators:
% 5.76/2.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.76/2.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.76/2.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.76/2.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.76/2.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.76/2.15  tff('#skF_7', type, '#skF_7': $i).
% 5.76/2.15  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.76/2.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.76/2.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.76/2.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.76/2.15  tff('#skF_5', type, '#skF_5': $i).
% 5.76/2.15  tff('#skF_6', type, '#skF_6': $i).
% 5.76/2.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.76/2.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.76/2.15  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.76/2.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.76/2.15  tff('#skF_4', type, '#skF_4': $i).
% 5.76/2.15  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.76/2.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.76/2.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.76/2.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.76/2.15  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.76/2.15  
% 5.76/2.16  tff(f_107, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 5.76/2.16  tff(f_88, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.76/2.16  tff(f_86, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 5.76/2.16  tff(f_98, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 5.76/2.16  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.76/2.16  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 5.76/2.16  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.76/2.16  tff(f_75, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_xboole_1)).
% 5.76/2.16  tff(f_69, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 5.76/2.16  tff(f_71, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.76/2.16  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.76/2.16  tff(f_67, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.76/2.16  tff(f_63, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 5.76/2.16  tff(f_55, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.76/2.16  tff(c_70, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.76/2.16  tff(c_87, plain, (![A_53]: (k2_tarski(A_53, A_53)=k1_tarski(A_53))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.76/2.16  tff(c_40, plain, (![D_36, B_32]: (r2_hidden(D_36, k2_tarski(D_36, B_32)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.76/2.16  tff(c_93, plain, (![A_53]: (r2_hidden(A_53, k1_tarski(A_53)))), inference(superposition, [status(thm), theory('equality')], [c_87, c_40])).
% 5.76/2.16  tff(c_72, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.76/2.16  tff(c_1496, plain, (![B_133, A_134]: (k1_tarski(B_133)=A_134 | k1_xboole_0=A_134 | ~r1_tarski(A_134, k1_tarski(B_133)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.76/2.16  tff(c_1518, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_7') | k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_72, c_1496])).
% 5.76/2.16  tff(c_1525, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1518])).
% 5.76/2.16  tff(c_239, plain, (![A_70, B_71]: (r1_xboole_0(A_70, B_71) | k3_xboole_0(A_70, B_71)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.76/2.16  tff(c_10, plain, (![B_8, A_7]: (r1_xboole_0(B_8, A_7) | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.76/2.16  tff(c_249, plain, (![B_71, A_70]: (r1_xboole_0(B_71, A_70) | k3_xboole_0(A_70, B_71)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_239, c_10])).
% 5.76/2.16  tff(c_68, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.76/2.16  tff(c_212, plain, (![A_68, B_69]: (k3_xboole_0(A_68, B_69)=k1_xboole_0 | ~r1_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.76/2.16  tff(c_227, plain, (k3_xboole_0('#skF_6', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_68, c_212])).
% 5.76/2.16  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.76/2.16  tff(c_2209, plain, (![A_154, B_155, C_156]: (k3_xboole_0(A_154, k2_xboole_0(B_155, C_156))=k3_xboole_0(A_154, C_156) | ~r1_xboole_0(A_154, B_155))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.76/2.16  tff(c_66, plain, (~r1_xboole_0(k2_xboole_0('#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.76/2.16  tff(c_247, plain, (k3_xboole_0(k2_xboole_0('#skF_4', '#skF_6'), '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_239, c_66])).
% 5.76/2.16  tff(c_251, plain, (k3_xboole_0('#skF_5', k2_xboole_0('#skF_4', '#skF_6'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4, c_247])).
% 5.76/2.16  tff(c_2285, plain, (k3_xboole_0('#skF_5', '#skF_6')!=k1_xboole_0 | ~r1_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2209, c_251])).
% 5.76/2.16  tff(c_2353, plain, (~r1_xboole_0('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_227, c_4, c_2285])).
% 5.76/2.16  tff(c_2379, plain, (k3_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_249, c_2353])).
% 5.76/2.16  tff(c_2390, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1525, c_2379])).
% 5.76/2.16  tff(c_2391, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_7')), inference(splitRight, [status(thm)], [c_1518])).
% 5.76/2.16  tff(c_28, plain, (![A_24]: (k4_xboole_0(A_24, k1_xboole_0)=A_24)), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.76/2.16  tff(c_30, plain, (![A_25]: (r1_xboole_0(A_25, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.76/2.16  tff(c_228, plain, (![A_25]: (k3_xboole_0(A_25, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_212])).
% 5.76/2.16  tff(c_414, plain, (![A_83, B_84]: (k5_xboole_0(A_83, k3_xboole_0(A_83, B_84))=k4_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.76/2.16  tff(c_429, plain, (![A_25]: (k5_xboole_0(A_25, k1_xboole_0)=k4_xboole_0(A_25, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_228, c_414])).
% 5.76/2.16  tff(c_441, plain, (![A_25]: (k5_xboole_0(A_25, k1_xboole_0)=A_25)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_429])).
% 5.76/2.16  tff(c_138, plain, (![B_59, A_60]: (r1_xboole_0(B_59, A_60) | ~r1_xboole_0(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.76/2.16  tff(c_143, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_68, c_138])).
% 5.76/2.16  tff(c_226, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_143, c_212])).
% 5.76/2.16  tff(c_426, plain, (k5_xboole_0('#skF_5', k1_xboole_0)=k4_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_226, c_414])).
% 5.76/2.16  tff(c_563, plain, (k4_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_441, c_426])).
% 5.76/2.16  tff(c_26, plain, (![A_22, B_23]: (r1_tarski(k3_xboole_0(A_22, B_23), A_22))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.76/2.16  tff(c_357, plain, (![A_75, C_76, B_77]: (r1_xboole_0(A_75, C_76) | ~r1_tarski(A_75, k4_xboole_0(B_77, C_76)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.76/2.16  tff(c_376, plain, (![B_77, C_76, B_23]: (r1_xboole_0(k3_xboole_0(k4_xboole_0(B_77, C_76), B_23), C_76))), inference(resolution, [status(thm)], [c_26, c_357])).
% 5.76/2.16  tff(c_574, plain, (![B_92]: (r1_xboole_0(k3_xboole_0('#skF_5', B_92), '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_563, c_376])).
% 5.76/2.16  tff(c_588, plain, (![B_4]: (r1_xboole_0(k3_xboole_0(B_4, '#skF_5'), '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_4, c_574])).
% 5.76/2.16  tff(c_2402, plain, (r1_xboole_0(k1_tarski('#skF_7'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2391, c_588])).
% 5.76/2.16  tff(c_12, plain, (![A_9, B_10, C_13]: (~r1_xboole_0(A_9, B_10) | ~r2_hidden(C_13, B_10) | ~r2_hidden(C_13, A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.76/2.16  tff(c_5436, plain, (![C_6577]: (~r2_hidden(C_6577, '#skF_6') | ~r2_hidden(C_6577, k1_tarski('#skF_7')))), inference(resolution, [status(thm)], [c_2402, c_12])).
% 5.76/2.16  tff(c_5448, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_93, c_5436])).
% 5.76/2.16  tff(c_5454, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_5448])).
% 5.76/2.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.76/2.16  
% 5.76/2.16  Inference rules
% 5.76/2.16  ----------------------
% 5.76/2.16  #Ref     : 0
% 5.76/2.16  #Sup     : 1167
% 5.76/2.16  #Fact    : 4
% 5.76/2.16  #Define  : 0
% 5.76/2.16  #Split   : 1
% 5.76/2.16  #Chain   : 0
% 5.76/2.16  #Close   : 0
% 5.76/2.16  
% 5.76/2.16  Ordering : KBO
% 5.76/2.16  
% 5.76/2.16  Simplification rules
% 5.76/2.16  ----------------------
% 5.76/2.16  #Subsume      : 26
% 5.76/2.16  #Demod        : 731
% 5.76/2.16  #Tautology    : 701
% 5.76/2.16  #SimpNegUnit  : 0
% 5.76/2.16  #BackRed      : 3
% 5.76/2.16  
% 5.76/2.16  #Partial instantiations: 3920
% 5.76/2.16  #Strategies tried      : 1
% 5.76/2.16  
% 5.76/2.16  Timing (in seconds)
% 5.76/2.16  ----------------------
% 5.76/2.17  Preprocessing        : 0.34
% 5.76/2.17  Parsing              : 0.18
% 5.76/2.17  CNF conversion       : 0.02
% 5.76/2.17  Main loop            : 0.99
% 5.76/2.17  Inferencing          : 0.36
% 5.76/2.17  Reduction            : 0.40
% 5.76/2.17  Demodulation         : 0.33
% 5.76/2.17  BG Simplification    : 0.03
% 5.76/2.17  Subsumption          : 0.14
% 5.76/2.17  Abstraction          : 0.04
% 5.76/2.17  MUC search           : 0.00
% 5.76/2.17  Cooper               : 0.00
% 5.76/2.17  Total                : 1.36
% 5.76/2.17  Index Insertion      : 0.00
% 5.76/2.17  Index Deletion       : 0.00
% 5.76/2.17  Index Matching       : 0.00
% 5.76/2.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
