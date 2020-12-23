%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:04 EST 2020

% Result     : Theorem 6.24s
% Output     : CNFRefutation 6.24s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 100 expanded)
%              Number of leaves         :   37 (  51 expanded)
%              Depth                    :    7
%              Number of atoms          :   81 ( 132 expanded)
%              Number of equality atoms :   41 (  62 expanded)
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

tff(f_107,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_96,axiom,(
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

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_57,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

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

tff(c_74,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_5'),k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_389,plain,(
    ! [B_104,A_105] :
      ( k1_tarski(B_104) = A_105
      | k1_xboole_0 = A_105
      | ~ r1_tarski(A_105,k1_tarski(B_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_411,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_7')
    | k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_74,c_389])).

tff(c_424,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_411])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    r1_xboole_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_265,plain,(
    ! [A_83,B_84] :
      ( k3_xboole_0(A_83,B_84) = k1_xboole_0
      | ~ r1_xboole_0(A_83,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_269,plain,(
    k3_xboole_0('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_70,c_265])).

tff(c_1481,plain,(
    ! [A_136,B_137,C_138] :
      ( k3_xboole_0(A_136,k2_xboole_0(B_137,C_138)) = k3_xboole_0(A_136,C_138)
      | ~ r1_xboole_0(A_136,B_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_305,plain,(
    ! [A_90,B_91] :
      ( r1_xboole_0(A_90,B_91)
      | k3_xboole_0(A_90,B_91) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_311,plain,(
    k3_xboole_0(k2_xboole_0('#skF_4','#skF_6'),'#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_305,c_68])).

tff(c_314,plain,(
    k3_xboole_0('#skF_5',k2_xboole_0('#skF_4','#skF_6')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_311])).

tff(c_1520,plain,
    ( k3_xboole_0('#skF_5','#skF_6') != k1_xboole_0
    | ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1481,c_314])).

tff(c_1569,plain,(
    ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_2,c_1520])).

tff(c_1577,plain,(
    k3_xboole_0('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_1569])).

tff(c_1581,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_424,c_2,c_1577])).

tff(c_1582,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_411])).

tff(c_78,plain,(
    ! [A_61,B_62] : r1_tarski(k3_xboole_0(A_61,B_62),A_61) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,(
    ! [A_15] :
      ( k1_xboole_0 = A_15
      | ~ r1_tarski(A_15,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_83,plain,(
    ! [B_62] : k3_xboole_0(k1_xboole_0,B_62) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_78,c_18])).

tff(c_1597,plain,(
    ! [A_139,B_140,C_141] : k3_xboole_0(k3_xboole_0(A_139,B_140),C_141) = k3_xboole_0(A_139,k3_xboole_0(B_140,C_141)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1634,plain,(
    ! [C_141] : k3_xboole_0('#skF_6',k3_xboole_0('#skF_5',C_141)) = k3_xboole_0(k1_xboole_0,C_141) ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_1597])).

tff(c_1669,plain,(
    ! [C_142] : k3_xboole_0('#skF_6',k3_xboole_0('#skF_5',C_142)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_1634])).

tff(c_1703,plain,(
    ! [B_143] : k3_xboole_0('#skF_6',k3_xboole_0(B_143,'#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1669])).

tff(c_1728,plain,(
    k3_xboole_0('#skF_6',k1_tarski('#skF_7')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1582,c_1703])).

tff(c_46,plain,(
    ! [A_26] : k2_tarski(A_26,A_26) = k1_tarski(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_270,plain,(
    ! [A_85,B_86] : k1_enumset1(A_85,A_85,B_86) = k2_tarski(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_26,plain,(
    ! [E_25,A_19,C_21] : r2_hidden(E_25,k1_enumset1(A_19,E_25,C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_300,plain,(
    ! [A_87,B_88] : r2_hidden(A_87,k2_tarski(A_87,B_88)) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_26])).

tff(c_303,plain,(
    ! [A_26] : r2_hidden(A_26,k1_tarski(A_26)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_300])).

tff(c_72,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_323,plain,(
    ! [A_98,B_99,C_100] :
      ( ~ r1_xboole_0(A_98,B_99)
      | ~ r2_hidden(C_100,B_99)
      | ~ r2_hidden(C_100,A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8068,plain,(
    ! [C_9715,B_9716,A_9717] :
      ( ~ r2_hidden(C_9715,B_9716)
      | ~ r2_hidden(C_9715,A_9717)
      | k3_xboole_0(A_9717,B_9716) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_323])).

tff(c_8096,plain,(
    ! [A_9820] :
      ( ~ r2_hidden('#skF_7',A_9820)
      | k3_xboole_0(A_9820,'#skF_6') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_72,c_8068])).

tff(c_8104,plain,(
    k3_xboole_0(k1_tarski('#skF_7'),'#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_303,c_8096])).

tff(c_8129,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1728,c_2,c_8104])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:37:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.24/2.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.24/2.33  
% 6.24/2.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.24/2.34  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 6.24/2.34  
% 6.24/2.34  %Foreground sorts:
% 6.24/2.34  
% 6.24/2.34  
% 6.24/2.34  %Background operators:
% 6.24/2.34  
% 6.24/2.34  
% 6.24/2.34  %Foreground operators:
% 6.24/2.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.24/2.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.24/2.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.24/2.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.24/2.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.24/2.34  tff('#skF_7', type, '#skF_7': $i).
% 6.24/2.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.24/2.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.24/2.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.24/2.34  tff('#skF_5', type, '#skF_5': $i).
% 6.24/2.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 6.24/2.34  tff('#skF_6', type, '#skF_6': $i).
% 6.24/2.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.24/2.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.24/2.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.24/2.34  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.24/2.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.24/2.34  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.24/2.34  tff('#skF_4', type, '#skF_4': $i).
% 6.24/2.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.24/2.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.24/2.34  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 6.24/2.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.24/2.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.24/2.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.24/2.34  
% 6.24/2.35  tff(f_107, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 6.24/2.35  tff(f_96, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 6.24/2.35  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.24/2.35  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 6.24/2.35  tff(f_61, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_xboole_1)).
% 6.24/2.35  tff(f_53, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 6.24/2.35  tff(f_57, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 6.24/2.35  tff(f_51, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 6.24/2.35  tff(f_78, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.24/2.35  tff(f_80, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 6.24/2.35  tff(f_76, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 6.24/2.35  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.24/2.35  tff(c_74, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.24/2.35  tff(c_389, plain, (![B_104, A_105]: (k1_tarski(B_104)=A_105 | k1_xboole_0=A_105 | ~r1_tarski(A_105, k1_tarski(B_104)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.24/2.35  tff(c_411, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_7') | k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_74, c_389])).
% 6.24/2.35  tff(c_424, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_411])).
% 6.24/2.35  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.24/2.35  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.24/2.35  tff(c_70, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.24/2.35  tff(c_265, plain, (![A_83, B_84]: (k3_xboole_0(A_83, B_84)=k1_xboole_0 | ~r1_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.24/2.35  tff(c_269, plain, (k3_xboole_0('#skF_6', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_70, c_265])).
% 6.24/2.35  tff(c_1481, plain, (![A_136, B_137, C_138]: (k3_xboole_0(A_136, k2_xboole_0(B_137, C_138))=k3_xboole_0(A_136, C_138) | ~r1_xboole_0(A_136, B_137))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.24/2.35  tff(c_305, plain, (![A_90, B_91]: (r1_xboole_0(A_90, B_91) | k3_xboole_0(A_90, B_91)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.24/2.35  tff(c_68, plain, (~r1_xboole_0(k2_xboole_0('#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.24/2.35  tff(c_311, plain, (k3_xboole_0(k2_xboole_0('#skF_4', '#skF_6'), '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_305, c_68])).
% 6.24/2.35  tff(c_314, plain, (k3_xboole_0('#skF_5', k2_xboole_0('#skF_4', '#skF_6'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_311])).
% 6.24/2.35  tff(c_1520, plain, (k3_xboole_0('#skF_5', '#skF_6')!=k1_xboole_0 | ~r1_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1481, c_314])).
% 6.24/2.35  tff(c_1569, plain, (~r1_xboole_0('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_269, c_2, c_1520])).
% 6.24/2.35  tff(c_1577, plain, (k3_xboole_0('#skF_5', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_1569])).
% 6.24/2.35  tff(c_1581, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_424, c_2, c_1577])).
% 6.24/2.35  tff(c_1582, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_7')), inference(splitRight, [status(thm)], [c_411])).
% 6.24/2.35  tff(c_78, plain, (![A_61, B_62]: (r1_tarski(k3_xboole_0(A_61, B_62), A_61))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.24/2.35  tff(c_18, plain, (![A_15]: (k1_xboole_0=A_15 | ~r1_tarski(A_15, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.24/2.35  tff(c_83, plain, (![B_62]: (k3_xboole_0(k1_xboole_0, B_62)=k1_xboole_0)), inference(resolution, [status(thm)], [c_78, c_18])).
% 6.24/2.35  tff(c_1597, plain, (![A_139, B_140, C_141]: (k3_xboole_0(k3_xboole_0(A_139, B_140), C_141)=k3_xboole_0(A_139, k3_xboole_0(B_140, C_141)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.24/2.35  tff(c_1634, plain, (![C_141]: (k3_xboole_0('#skF_6', k3_xboole_0('#skF_5', C_141))=k3_xboole_0(k1_xboole_0, C_141))), inference(superposition, [status(thm), theory('equality')], [c_269, c_1597])).
% 6.24/2.35  tff(c_1669, plain, (![C_142]: (k3_xboole_0('#skF_6', k3_xboole_0('#skF_5', C_142))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_83, c_1634])).
% 6.24/2.35  tff(c_1703, plain, (![B_143]: (k3_xboole_0('#skF_6', k3_xboole_0(B_143, '#skF_5'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1669])).
% 6.24/2.35  tff(c_1728, plain, (k3_xboole_0('#skF_6', k1_tarski('#skF_7'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1582, c_1703])).
% 6.24/2.35  tff(c_46, plain, (![A_26]: (k2_tarski(A_26, A_26)=k1_tarski(A_26))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.24/2.35  tff(c_270, plain, (![A_85, B_86]: (k1_enumset1(A_85, A_85, B_86)=k2_tarski(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.24/2.35  tff(c_26, plain, (![E_25, A_19, C_21]: (r2_hidden(E_25, k1_enumset1(A_19, E_25, C_21)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.24/2.35  tff(c_300, plain, (![A_87, B_88]: (r2_hidden(A_87, k2_tarski(A_87, B_88)))), inference(superposition, [status(thm), theory('equality')], [c_270, c_26])).
% 6.24/2.35  tff(c_303, plain, (![A_26]: (r2_hidden(A_26, k1_tarski(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_300])).
% 6.24/2.35  tff(c_72, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.24/2.35  tff(c_323, plain, (![A_98, B_99, C_100]: (~r1_xboole_0(A_98, B_99) | ~r2_hidden(C_100, B_99) | ~r2_hidden(C_100, A_98))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.24/2.35  tff(c_8068, plain, (![C_9715, B_9716, A_9717]: (~r2_hidden(C_9715, B_9716) | ~r2_hidden(C_9715, A_9717) | k3_xboole_0(A_9717, B_9716)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_323])).
% 6.24/2.35  tff(c_8096, plain, (![A_9820]: (~r2_hidden('#skF_7', A_9820) | k3_xboole_0(A_9820, '#skF_6')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_72, c_8068])).
% 6.24/2.35  tff(c_8104, plain, (k3_xboole_0(k1_tarski('#skF_7'), '#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_303, c_8096])).
% 6.24/2.35  tff(c_8129, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1728, c_2, c_8104])).
% 6.24/2.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.24/2.35  
% 6.24/2.35  Inference rules
% 6.24/2.35  ----------------------
% 6.24/2.35  #Ref     : 0
% 6.24/2.35  #Sup     : 1730
% 6.24/2.35  #Fact    : 12
% 6.24/2.35  #Define  : 0
% 6.24/2.35  #Split   : 1
% 6.24/2.35  #Chain   : 0
% 6.24/2.35  #Close   : 0
% 6.24/2.35  
% 6.24/2.35  Ordering : KBO
% 6.24/2.35  
% 6.24/2.35  Simplification rules
% 6.24/2.35  ----------------------
% 6.24/2.35  #Subsume      : 48
% 6.24/2.35  #Demod        : 1925
% 6.24/2.35  #Tautology    : 1214
% 6.24/2.35  #SimpNegUnit  : 0
% 6.24/2.35  #BackRed      : 3
% 6.24/2.35  
% 6.24/2.35  #Partial instantiations: 3572
% 6.24/2.35  #Strategies tried      : 1
% 6.24/2.35  
% 6.24/2.35  Timing (in seconds)
% 6.24/2.35  ----------------------
% 6.24/2.35  Preprocessing        : 0.34
% 6.24/2.35  Parsing              : 0.18
% 6.24/2.35  CNF conversion       : 0.03
% 6.24/2.35  Main loop            : 1.23
% 6.24/2.35  Inferencing          : 0.44
% 6.24/2.35  Reduction            : 0.54
% 6.24/2.35  Demodulation         : 0.46
% 6.24/2.35  BG Simplification    : 0.04
% 6.24/2.35  Subsumption          : 0.15
% 6.24/2.35  Abstraction          : 0.05
% 6.24/2.35  MUC search           : 0.00
% 6.24/2.35  Cooper               : 0.00
% 6.24/2.35  Total                : 1.60
% 6.24/2.35  Index Insertion      : 0.00
% 6.24/2.35  Index Deletion       : 0.00
% 6.24/2.35  Index Matching       : 0.00
% 6.24/2.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
