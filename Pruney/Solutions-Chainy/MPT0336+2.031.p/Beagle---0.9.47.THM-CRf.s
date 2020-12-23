%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:04 EST 2020

% Result     : Theorem 8.97s
% Output     : CNFRefutation 9.09s
% Verified   : 
% Statistics : Number of formulae       :   74 (  99 expanded)
%              Number of leaves         :   36 (  50 expanded)
%              Depth                    :    7
%              Number of atoms          :   81 ( 132 expanded)
%              Number of equality atoms :   41 (  62 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_105,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_57,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_78,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_80,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_49,axiom,(
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

tff(c_72,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_5'),k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_308,plain,(
    ! [B_91,A_92] :
      ( k1_tarski(B_91) = A_92
      | k1_xboole_0 = A_92
      | ~ r1_tarski(A_92,k1_tarski(B_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_319,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_7')
    | k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_72,c_308])).

tff(c_355,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_319])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    r1_xboole_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_189,plain,(
    ! [A_69,B_70] :
      ( k3_xboole_0(A_69,B_70) = k1_xboole_0
      | ~ r1_xboole_0(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_193,plain,(
    k3_xboole_0('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_68,c_189])).

tff(c_1076,plain,(
    ! [A_120,B_121,C_122] :
      ( k3_xboole_0(A_120,k2_xboole_0(B_121,C_122)) = k3_xboole_0(A_120,C_122)
      | ~ r1_xboole_0(A_120,B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_245,plain,(
    ! [A_78,B_79] :
      ( r1_xboole_0(A_78,B_79)
      | k3_xboole_0(A_78,B_79) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_251,plain,(
    k3_xboole_0(k2_xboole_0('#skF_4','#skF_6'),'#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_245,c_66])).

tff(c_254,plain,(
    k3_xboole_0('#skF_5',k2_xboole_0('#skF_4','#skF_6')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_251])).

tff(c_1109,plain,
    ( k3_xboole_0('#skF_5','#skF_6') != k1_xboole_0
    | ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1076,c_254])).

tff(c_1151,plain,(
    ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_2,c_1109])).

tff(c_1158,plain,(
    k3_xboole_0('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_1151])).

tff(c_1162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_355,c_2,c_1158])).

tff(c_1163,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_319])).

tff(c_18,plain,(
    ! [A_15] : r1_tarski(k1_xboole_0,A_15) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_121,plain,(
    ! [A_65,B_66] :
      ( k3_xboole_0(A_65,B_66) = A_65
      | ~ r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_133,plain,(
    ! [A_15] : k3_xboole_0(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_121])).

tff(c_1206,plain,(
    ! [A_123,B_124,C_125] : k3_xboole_0(k3_xboole_0(A_123,B_124),C_125) = k3_xboole_0(A_123,k3_xboole_0(B_124,C_125)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1240,plain,(
    ! [C_125] : k3_xboole_0('#skF_6',k3_xboole_0('#skF_5',C_125)) = k3_xboole_0(k1_xboole_0,C_125) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_1206])).

tff(c_1275,plain,(
    ! [C_126] : k3_xboole_0('#skF_6',k3_xboole_0('#skF_5',C_126)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_1240])).

tff(c_1301,plain,(
    ! [B_127] : k3_xboole_0('#skF_6',k3_xboole_0(B_127,'#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1275])).

tff(c_1320,plain,(
    k3_xboole_0('#skF_6',k1_tarski('#skF_7')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1163,c_1301])).

tff(c_46,plain,(
    ! [A_26] : k2_tarski(A_26,A_26) = k1_tarski(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_216,plain,(
    ! [A_71,B_72] : k1_enumset1(A_71,A_71,B_72) = k2_tarski(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_28,plain,(
    ! [E_25,B_20,C_21] : r2_hidden(E_25,k1_enumset1(E_25,B_20,C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_234,plain,(
    ! [A_73,B_74] : r2_hidden(A_73,k2_tarski(A_73,B_74)) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_28])).

tff(c_237,plain,(
    ! [A_26] : r2_hidden(A_26,k1_tarski(A_26)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_234])).

tff(c_70,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_324,plain,(
    ! [A_93,B_94,C_95] :
      ( ~ r1_xboole_0(A_93,B_94)
      | ~ r2_hidden(C_95,B_94)
      | ~ r2_hidden(C_95,A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_11232,plain,(
    ! [C_12821,B_12822,A_12823] :
      ( ~ r2_hidden(C_12821,B_12822)
      | ~ r2_hidden(C_12821,A_12823)
      | k3_xboole_0(A_12823,B_12822) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_324])).

tff(c_11263,plain,(
    ! [A_12953] :
      ( ~ r2_hidden('#skF_7',A_12953)
      | k3_xboole_0(A_12953,'#skF_6') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_70,c_11232])).

tff(c_11271,plain,(
    k3_xboole_0(k1_tarski('#skF_7'),'#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_237,c_11263])).

tff(c_11296,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1320,c_2,c_11271])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:41:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.97/2.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.97/2.94  
% 8.97/2.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.97/2.95  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 8.97/2.95  
% 8.97/2.95  %Foreground sorts:
% 8.97/2.95  
% 8.97/2.95  
% 8.97/2.95  %Background operators:
% 8.97/2.95  
% 8.97/2.95  
% 8.97/2.95  %Foreground operators:
% 8.97/2.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.97/2.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.97/2.95  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.97/2.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.97/2.95  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.97/2.95  tff('#skF_7', type, '#skF_7': $i).
% 8.97/2.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.97/2.95  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.97/2.95  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.97/2.95  tff('#skF_5', type, '#skF_5': $i).
% 8.97/2.95  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 8.97/2.95  tff('#skF_6', type, '#skF_6': $i).
% 8.97/2.95  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.97/2.95  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.97/2.95  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.97/2.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.97/2.95  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.97/2.95  tff('#skF_4', type, '#skF_4': $i).
% 8.97/2.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.97/2.95  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.97/2.95  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 8.97/2.95  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.97/2.95  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.97/2.95  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.97/2.95  
% 9.09/2.96  tff(f_105, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 9.09/2.96  tff(f_94, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 9.09/2.96  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.09/2.96  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 9.09/2.96  tff(f_61, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_xboole_1)).
% 9.09/2.96  tff(f_57, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.09/2.96  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.09/2.96  tff(f_51, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 9.09/2.96  tff(f_78, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 9.09/2.96  tff(f_80, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 9.09/2.96  tff(f_76, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 9.09/2.96  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 9.09/2.96  tff(c_72, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.09/2.96  tff(c_308, plain, (![B_91, A_92]: (k1_tarski(B_91)=A_92 | k1_xboole_0=A_92 | ~r1_tarski(A_92, k1_tarski(B_91)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 9.09/2.96  tff(c_319, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_7') | k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_72, c_308])).
% 9.09/2.96  tff(c_355, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_319])).
% 9.09/2.96  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.09/2.96  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.09/2.96  tff(c_68, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.09/2.96  tff(c_189, plain, (![A_69, B_70]: (k3_xboole_0(A_69, B_70)=k1_xboole_0 | ~r1_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.09/2.96  tff(c_193, plain, (k3_xboole_0('#skF_6', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_68, c_189])).
% 9.09/2.96  tff(c_1076, plain, (![A_120, B_121, C_122]: (k3_xboole_0(A_120, k2_xboole_0(B_121, C_122))=k3_xboole_0(A_120, C_122) | ~r1_xboole_0(A_120, B_121))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.09/2.96  tff(c_245, plain, (![A_78, B_79]: (r1_xboole_0(A_78, B_79) | k3_xboole_0(A_78, B_79)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.09/2.96  tff(c_66, plain, (~r1_xboole_0(k2_xboole_0('#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.09/2.96  tff(c_251, plain, (k3_xboole_0(k2_xboole_0('#skF_4', '#skF_6'), '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_245, c_66])).
% 9.09/2.96  tff(c_254, plain, (k3_xboole_0('#skF_5', k2_xboole_0('#skF_4', '#skF_6'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_251])).
% 9.09/2.96  tff(c_1109, plain, (k3_xboole_0('#skF_5', '#skF_6')!=k1_xboole_0 | ~r1_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1076, c_254])).
% 9.09/2.96  tff(c_1151, plain, (~r1_xboole_0('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_193, c_2, c_1109])).
% 9.09/2.96  tff(c_1158, plain, (k3_xboole_0('#skF_5', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_1151])).
% 9.09/2.96  tff(c_1162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_355, c_2, c_1158])).
% 9.09/2.96  tff(c_1163, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_7')), inference(splitRight, [status(thm)], [c_319])).
% 9.09/2.96  tff(c_18, plain, (![A_15]: (r1_tarski(k1_xboole_0, A_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.09/2.96  tff(c_121, plain, (![A_65, B_66]: (k3_xboole_0(A_65, B_66)=A_65 | ~r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.09/2.96  tff(c_133, plain, (![A_15]: (k3_xboole_0(k1_xboole_0, A_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_121])).
% 9.09/2.96  tff(c_1206, plain, (![A_123, B_124, C_125]: (k3_xboole_0(k3_xboole_0(A_123, B_124), C_125)=k3_xboole_0(A_123, k3_xboole_0(B_124, C_125)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.09/2.96  tff(c_1240, plain, (![C_125]: (k3_xboole_0('#skF_6', k3_xboole_0('#skF_5', C_125))=k3_xboole_0(k1_xboole_0, C_125))), inference(superposition, [status(thm), theory('equality')], [c_193, c_1206])).
% 9.09/2.96  tff(c_1275, plain, (![C_126]: (k3_xboole_0('#skF_6', k3_xboole_0('#skF_5', C_126))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_133, c_1240])).
% 9.09/2.96  tff(c_1301, plain, (![B_127]: (k3_xboole_0('#skF_6', k3_xboole_0(B_127, '#skF_5'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1275])).
% 9.09/2.96  tff(c_1320, plain, (k3_xboole_0('#skF_6', k1_tarski('#skF_7'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1163, c_1301])).
% 9.09/2.96  tff(c_46, plain, (![A_26]: (k2_tarski(A_26, A_26)=k1_tarski(A_26))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.09/2.96  tff(c_216, plain, (![A_71, B_72]: (k1_enumset1(A_71, A_71, B_72)=k2_tarski(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.09/2.96  tff(c_28, plain, (![E_25, B_20, C_21]: (r2_hidden(E_25, k1_enumset1(E_25, B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.09/2.96  tff(c_234, plain, (![A_73, B_74]: (r2_hidden(A_73, k2_tarski(A_73, B_74)))), inference(superposition, [status(thm), theory('equality')], [c_216, c_28])).
% 9.09/2.96  tff(c_237, plain, (![A_26]: (r2_hidden(A_26, k1_tarski(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_234])).
% 9.09/2.96  tff(c_70, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.09/2.96  tff(c_324, plain, (![A_93, B_94, C_95]: (~r1_xboole_0(A_93, B_94) | ~r2_hidden(C_95, B_94) | ~r2_hidden(C_95, A_93))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.09/2.96  tff(c_11232, plain, (![C_12821, B_12822, A_12823]: (~r2_hidden(C_12821, B_12822) | ~r2_hidden(C_12821, A_12823) | k3_xboole_0(A_12823, B_12822)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_324])).
% 9.09/2.96  tff(c_11263, plain, (![A_12953]: (~r2_hidden('#skF_7', A_12953) | k3_xboole_0(A_12953, '#skF_6')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_70, c_11232])).
% 9.09/2.96  tff(c_11271, plain, (k3_xboole_0(k1_tarski('#skF_7'), '#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_237, c_11263])).
% 9.09/2.96  tff(c_11296, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1320, c_2, c_11271])).
% 9.09/2.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.09/2.96  
% 9.09/2.96  Inference rules
% 9.09/2.96  ----------------------
% 9.09/2.96  #Ref     : 0
% 9.09/2.96  #Sup     : 2366
% 9.09/2.96  #Fact    : 18
% 9.09/2.96  #Define  : 0
% 9.09/2.96  #Split   : 1
% 9.09/2.96  #Chain   : 0
% 9.09/2.96  #Close   : 0
% 9.09/2.96  
% 9.09/2.96  Ordering : KBO
% 9.09/2.96  
% 9.09/2.96  Simplification rules
% 9.09/2.96  ----------------------
% 9.09/2.96  #Subsume      : 103
% 9.09/2.96  #Demod        : 2763
% 9.09/2.96  #Tautology    : 1625
% 9.09/2.96  #SimpNegUnit  : 0
% 9.09/2.96  #BackRed      : 8
% 9.09/2.96  
% 9.09/2.96  #Partial instantiations: 5346
% 9.09/2.96  #Strategies tried      : 1
% 9.09/2.96  
% 9.09/2.96  Timing (in seconds)
% 9.09/2.96  ----------------------
% 9.09/2.96  Preprocessing        : 0.35
% 9.09/2.96  Parsing              : 0.18
% 9.09/2.96  CNF conversion       : 0.03
% 9.09/2.96  Main loop            : 1.84
% 9.09/2.96  Inferencing          : 0.62
% 9.09/2.96  Reduction            : 0.88
% 9.09/2.96  Demodulation         : 0.77
% 9.09/2.96  BG Simplification    : 0.06
% 9.09/2.96  Subsumption          : 0.21
% 9.09/2.96  Abstraction          : 0.07
% 9.09/2.96  MUC search           : 0.00
% 9.09/2.96  Cooper               : 0.00
% 9.09/2.97  Total                : 2.22
% 9.09/2.97  Index Insertion      : 0.00
% 9.09/2.97  Index Deletion       : 0.00
% 9.09/2.97  Index Matching       : 0.00
% 9.09/2.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
