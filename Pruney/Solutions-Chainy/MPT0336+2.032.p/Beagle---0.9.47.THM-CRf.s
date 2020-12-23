%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:04 EST 2020

% Result     : Theorem 7.07s
% Output     : CNFRefutation 7.07s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 103 expanded)
%              Number of leaves         :   36 (  52 expanded)
%              Depth                    :    7
%              Number of atoms          :   78 ( 135 expanded)
%              Number of equality atoms :   40 (  65 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_53,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_74,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_76,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_72,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_5'),k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_270,plain,(
    ! [B_94,A_95] :
      ( k1_tarski(B_94) = A_95
      | k1_xboole_0 = A_95
      | ~ r1_tarski(A_95,k1_tarski(B_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_280,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_7')
    | k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_72,c_270])).

tff(c_439,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_280])).

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
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_144,plain,(
    ! [A_76,B_77] :
      ( k3_xboole_0(A_76,B_77) = k1_xboole_0
      | ~ r1_xboole_0(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_152,plain,(
    k3_xboole_0('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_68,c_144])).

tff(c_588,plain,(
    ! [A_117,B_118,C_119] :
      ( k3_xboole_0(A_117,k2_xboole_0(B_118,C_119)) = k3_xboole_0(A_117,C_119)
      | ~ r1_xboole_0(A_117,B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_211,plain,(
    ! [A_80,B_81] :
      ( r1_xboole_0(A_80,B_81)
      | k3_xboole_0(A_80,B_81) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_217,plain,(
    k3_xboole_0(k2_xboole_0('#skF_4','#skF_6'),'#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_211,c_66])).

tff(c_220,plain,(
    k3_xboole_0('#skF_5',k2_xboole_0('#skF_4','#skF_6')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_217])).

tff(c_609,plain,
    ( k3_xboole_0('#skF_5','#skF_6') != k1_xboole_0
    | ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_588,c_220])).

tff(c_648,plain,(
    ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_2,c_609])).

tff(c_657,plain,(
    k3_xboole_0('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_648])).

tff(c_661,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_439,c_2,c_657])).

tff(c_662,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_280])).

tff(c_16,plain,(
    ! [A_13] : r1_xboole_0(A_13,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_153,plain,(
    ! [A_78] : k3_xboole_0(A_78,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_144])).

tff(c_158,plain,(
    ! [A_78] : k3_xboole_0(k1_xboole_0,A_78) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_2])).

tff(c_316,plain,(
    ! [A_102,B_103,C_104] : k3_xboole_0(k3_xboole_0(A_102,B_103),C_104) = k3_xboole_0(A_102,k3_xboole_0(B_103,C_104)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_344,plain,(
    ! [C_104] : k3_xboole_0('#skF_6',k3_xboole_0('#skF_5',C_104)) = k3_xboole_0(k1_xboole_0,C_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_316])).

tff(c_375,plain,(
    ! [C_105] : k3_xboole_0('#skF_6',k3_xboole_0('#skF_5',C_105)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_344])).

tff(c_389,plain,(
    ! [B_2] : k3_xboole_0('#skF_6',k3_xboole_0(B_2,'#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_375])).

tff(c_669,plain,(
    k3_xboole_0('#skF_6',k1_tarski('#skF_7')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_662,c_389])).

tff(c_44,plain,(
    ! [A_24] : k2_tarski(A_24,A_24) = k1_tarski(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_121,plain,(
    ! [A_71,B_72] : k1_enumset1(A_71,A_71,B_72) = k2_tarski(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_24,plain,(
    ! [E_23,A_17,C_19] : r2_hidden(E_23,k1_enumset1(A_17,E_23,C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_139,plain,(
    ! [A_73,B_74] : r2_hidden(A_73,k2_tarski(A_73,B_74)) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_24])).

tff(c_142,plain,(
    ! [A_24] : r2_hidden(A_24,k1_tarski(A_24)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_139])).

tff(c_70,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_285,plain,(
    ! [A_96,B_97,C_98] :
      ( ~ r1_xboole_0(A_96,B_97)
      | ~ r2_hidden(C_98,B_97)
      | ~ r2_hidden(C_98,A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_9930,plain,(
    ! [C_14853,B_14854,A_14855] :
      ( ~ r2_hidden(C_14853,B_14854)
      | ~ r2_hidden(C_14853,A_14855)
      | k3_xboole_0(A_14855,B_14854) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_285])).

tff(c_9961,plain,(
    ! [A_15009] :
      ( ~ r2_hidden('#skF_7',A_15009)
      | k3_xboole_0(A_15009,'#skF_6') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_70,c_9930])).

tff(c_9969,plain,(
    k3_xboole_0(k1_tarski('#skF_7'),'#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_142,c_9961])).

tff(c_9994,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_669,c_2,c_9969])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n020.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 10:40:22 EST 2020
% 0.16/0.31  % CPUTime    : 
% 0.16/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.07/2.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.07/2.50  
% 7.07/2.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.07/2.50  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 7.07/2.50  
% 7.07/2.50  %Foreground sorts:
% 7.07/2.50  
% 7.07/2.50  
% 7.07/2.50  %Background operators:
% 7.07/2.50  
% 7.07/2.50  
% 7.07/2.50  %Foreground operators:
% 7.07/2.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.07/2.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.07/2.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.07/2.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.07/2.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.07/2.50  tff('#skF_7', type, '#skF_7': $i).
% 7.07/2.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.07/2.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.07/2.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.07/2.50  tff('#skF_5', type, '#skF_5': $i).
% 7.07/2.50  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 7.07/2.50  tff('#skF_6', type, '#skF_6': $i).
% 7.07/2.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.07/2.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.07/2.50  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.07/2.50  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.07/2.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.07/2.50  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.07/2.50  tff('#skF_4', type, '#skF_4': $i).
% 7.07/2.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.07/2.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.07/2.50  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 7.07/2.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.07/2.50  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.07/2.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.07/2.50  
% 7.07/2.51  tff(f_103, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 7.07/2.51  tff(f_92, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 7.07/2.51  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.07/2.51  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.07/2.51  tff(f_57, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_xboole_1)).
% 7.07/2.51  tff(f_53, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 7.07/2.51  tff(f_51, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 7.07/2.51  tff(f_74, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 7.07/2.51  tff(f_76, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 7.07/2.51  tff(f_72, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 7.07/2.51  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 7.07/2.51  tff(c_72, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.07/2.51  tff(c_270, plain, (![B_94, A_95]: (k1_tarski(B_94)=A_95 | k1_xboole_0=A_95 | ~r1_tarski(A_95, k1_tarski(B_94)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.07/2.51  tff(c_280, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_7') | k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_72, c_270])).
% 7.07/2.51  tff(c_439, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_280])).
% 7.07/2.51  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.07/2.51  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.07/2.51  tff(c_68, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.07/2.51  tff(c_144, plain, (![A_76, B_77]: (k3_xboole_0(A_76, B_77)=k1_xboole_0 | ~r1_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.07/2.51  tff(c_152, plain, (k3_xboole_0('#skF_6', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_68, c_144])).
% 7.07/2.51  tff(c_588, plain, (![A_117, B_118, C_119]: (k3_xboole_0(A_117, k2_xboole_0(B_118, C_119))=k3_xboole_0(A_117, C_119) | ~r1_xboole_0(A_117, B_118))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.07/2.51  tff(c_211, plain, (![A_80, B_81]: (r1_xboole_0(A_80, B_81) | k3_xboole_0(A_80, B_81)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.07/2.51  tff(c_66, plain, (~r1_xboole_0(k2_xboole_0('#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.07/2.51  tff(c_217, plain, (k3_xboole_0(k2_xboole_0('#skF_4', '#skF_6'), '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_211, c_66])).
% 7.07/2.51  tff(c_220, plain, (k3_xboole_0('#skF_5', k2_xboole_0('#skF_4', '#skF_6'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_217])).
% 7.07/2.51  tff(c_609, plain, (k3_xboole_0('#skF_5', '#skF_6')!=k1_xboole_0 | ~r1_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_588, c_220])).
% 7.07/2.51  tff(c_648, plain, (~r1_xboole_0('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_152, c_2, c_609])).
% 7.07/2.51  tff(c_657, plain, (k3_xboole_0('#skF_5', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_648])).
% 7.07/2.51  tff(c_661, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_439, c_2, c_657])).
% 7.07/2.51  tff(c_662, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_7')), inference(splitRight, [status(thm)], [c_280])).
% 7.07/2.51  tff(c_16, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.07/2.51  tff(c_153, plain, (![A_78]: (k3_xboole_0(A_78, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_144])).
% 7.07/2.51  tff(c_158, plain, (![A_78]: (k3_xboole_0(k1_xboole_0, A_78)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_153, c_2])).
% 7.07/2.51  tff(c_316, plain, (![A_102, B_103, C_104]: (k3_xboole_0(k3_xboole_0(A_102, B_103), C_104)=k3_xboole_0(A_102, k3_xboole_0(B_103, C_104)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.07/2.51  tff(c_344, plain, (![C_104]: (k3_xboole_0('#skF_6', k3_xboole_0('#skF_5', C_104))=k3_xboole_0(k1_xboole_0, C_104))), inference(superposition, [status(thm), theory('equality')], [c_152, c_316])).
% 7.07/2.51  tff(c_375, plain, (![C_105]: (k3_xboole_0('#skF_6', k3_xboole_0('#skF_5', C_105))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_158, c_344])).
% 7.07/2.51  tff(c_389, plain, (![B_2]: (k3_xboole_0('#skF_6', k3_xboole_0(B_2, '#skF_5'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_375])).
% 7.07/2.51  tff(c_669, plain, (k3_xboole_0('#skF_6', k1_tarski('#skF_7'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_662, c_389])).
% 7.07/2.51  tff(c_44, plain, (![A_24]: (k2_tarski(A_24, A_24)=k1_tarski(A_24))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.07/2.51  tff(c_121, plain, (![A_71, B_72]: (k1_enumset1(A_71, A_71, B_72)=k2_tarski(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.07/2.51  tff(c_24, plain, (![E_23, A_17, C_19]: (r2_hidden(E_23, k1_enumset1(A_17, E_23, C_19)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.07/2.51  tff(c_139, plain, (![A_73, B_74]: (r2_hidden(A_73, k2_tarski(A_73, B_74)))), inference(superposition, [status(thm), theory('equality')], [c_121, c_24])).
% 7.07/2.51  tff(c_142, plain, (![A_24]: (r2_hidden(A_24, k1_tarski(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_139])).
% 7.07/2.51  tff(c_70, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.07/2.51  tff(c_285, plain, (![A_96, B_97, C_98]: (~r1_xboole_0(A_96, B_97) | ~r2_hidden(C_98, B_97) | ~r2_hidden(C_98, A_96))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.07/2.51  tff(c_9930, plain, (![C_14853, B_14854, A_14855]: (~r2_hidden(C_14853, B_14854) | ~r2_hidden(C_14853, A_14855) | k3_xboole_0(A_14855, B_14854)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_285])).
% 7.07/2.51  tff(c_9961, plain, (![A_15009]: (~r2_hidden('#skF_7', A_15009) | k3_xboole_0(A_15009, '#skF_6')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_70, c_9930])).
% 7.07/2.51  tff(c_9969, plain, (k3_xboole_0(k1_tarski('#skF_7'), '#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_142, c_9961])).
% 7.07/2.51  tff(c_9994, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_669, c_2, c_9969])).
% 7.07/2.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.07/2.51  
% 7.07/2.51  Inference rules
% 7.07/2.51  ----------------------
% 7.07/2.51  #Ref     : 0
% 7.07/2.51  #Sup     : 2025
% 7.07/2.51  #Fact    : 18
% 7.07/2.51  #Define  : 0
% 7.07/2.51  #Split   : 1
% 7.07/2.51  #Chain   : 0
% 7.07/2.51  #Close   : 0
% 7.07/2.51  
% 7.07/2.51  Ordering : KBO
% 7.07/2.51  
% 7.07/2.51  Simplification rules
% 7.07/2.51  ----------------------
% 7.07/2.51  #Subsume      : 102
% 7.07/2.51  #Demod        : 2329
% 7.07/2.51  #Tautology    : 1396
% 7.07/2.51  #SimpNegUnit  : 0
% 7.07/2.51  #BackRed      : 4
% 7.07/2.51  
% 7.07/2.51  #Partial instantiations: 5529
% 7.07/2.51  #Strategies tried      : 1
% 7.07/2.51  
% 7.07/2.51  Timing (in seconds)
% 7.07/2.51  ----------------------
% 7.46/2.52  Preprocessing        : 0.34
% 7.46/2.52  Parsing              : 0.18
% 7.46/2.52  CNF conversion       : 0.02
% 7.46/2.52  Main loop            : 1.46
% 7.46/2.52  Inferencing          : 0.54
% 7.46/2.52  Reduction            : 0.66
% 7.46/2.52  Demodulation         : 0.57
% 7.46/2.52  BG Simplification    : 0.05
% 7.46/2.52  Subsumption          : 0.16
% 7.46/2.52  Abstraction          : 0.06
% 7.46/2.52  MUC search           : 0.00
% 7.46/2.52  Cooper               : 0.00
% 7.46/2.52  Total                : 1.83
% 7.46/2.52  Index Insertion      : 0.00
% 7.46/2.52  Index Deletion       : 0.00
% 7.46/2.52  Index Matching       : 0.00
% 7.46/2.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
