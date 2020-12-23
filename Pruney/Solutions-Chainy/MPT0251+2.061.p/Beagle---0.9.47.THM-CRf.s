%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:54 EST 2020

% Result     : Theorem 3.59s
% Output     : CNFRefutation 4.01s
% Verified   : 
% Statistics : Number of formulae       :   70 (  76 expanded)
%              Number of leaves         :   36 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :   72 (  80 expanded)
%              Number of equality atoms :   34 (  40 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_75,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_43,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_65,axiom,(
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

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_87,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_83,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_79,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_64,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_34,plain,(
    ! [A_25] : k2_xboole_0(A_25,k1_xboole_0) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_16,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_380,plain,(
    ! [A_93,B_94] :
      ( r2_hidden('#skF_3'(A_93,B_94),A_93)
      | r1_xboole_0(A_93,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    ! [B_8,A_5] :
      ( ~ r2_hidden(B_8,A_5)
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_385,plain,(
    ! [A_95,B_96] :
      ( ~ v1_xboole_0(A_95)
      | r1_xboole_0(A_95,B_96) ) ),
    inference(resolution,[status(thm)],[c_380,c_6])).

tff(c_42,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(A_32,B_33) = A_32
      | ~ r1_xboole_0(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_526,plain,(
    ! [A_108,B_109] :
      ( k4_xboole_0(A_108,B_109) = A_108
      | ~ v1_xboole_0(A_108) ) ),
    inference(resolution,[status(thm)],[c_385,c_42])).

tff(c_529,plain,(
    ! [B_109] : k4_xboole_0(k1_xboole_0,B_109) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_526])).

tff(c_97,plain,(
    ! [B_58,A_59] : k2_xboole_0(B_58,A_59) = k2_xboole_0(A_59,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_113,plain,(
    ! [A_59] : k2_xboole_0(k1_xboole_0,A_59) = A_59 ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_34])).

tff(c_551,plain,(
    ! [A_111,B_112] : k4_xboole_0(k2_xboole_0(A_111,B_112),B_112) = k4_xboole_0(A_111,B_112) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_577,plain,(
    ! [A_59] : k4_xboole_0(k1_xboole_0,A_59) = k4_xboole_0(A_59,A_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_551])).

tff(c_592,plain,(
    ! [A_59] : k4_xboole_0(A_59,A_59) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_529,c_577])).

tff(c_30,plain,(
    ! [B_22] : r1_tarski(B_22,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_221,plain,(
    ! [A_65,B_66] :
      ( k3_xboole_0(A_65,B_66) = A_65
      | ~ r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_225,plain,(
    ! [B_22] : k3_xboole_0(B_22,B_22) = B_22 ),
    inference(resolution,[status(thm)],[c_30,c_221])).

tff(c_324,plain,(
    ! [A_85,B_86] : k5_xboole_0(A_85,k3_xboole_0(A_85,B_86)) = k4_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_333,plain,(
    ! [B_22] : k5_xboole_0(B_22,B_22) = k4_xboole_0(B_22,B_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_324])).

tff(c_594,plain,(
    ! [B_22] : k5_xboole_0(B_22,B_22) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_592,c_333])).

tff(c_287,plain,(
    ! [A_78,B_79] :
      ( r1_tarski(k1_tarski(A_78),B_79)
      | ~ r2_hidden(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_36,plain,(
    ! [A_26,B_27] :
      ( k3_xboole_0(A_26,B_27) = A_26
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2116,plain,(
    ! [A_182,B_183] :
      ( k3_xboole_0(k1_tarski(A_182),B_183) = k1_tarski(A_182)
      | ~ r2_hidden(A_182,B_183) ) ),
    inference(resolution,[status(thm)],[c_287,c_36])).

tff(c_32,plain,(
    ! [A_23,B_24] : k5_xboole_0(A_23,k3_xboole_0(A_23,B_24)) = k4_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2129,plain,(
    ! [A_182,B_183] :
      ( k5_xboole_0(k1_tarski(A_182),k1_tarski(A_182)) = k4_xboole_0(k1_tarski(A_182),B_183)
      | ~ r2_hidden(A_182,B_183) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2116,c_32])).

tff(c_2200,plain,(
    ! [A_185,B_186] :
      ( k4_xboole_0(k1_tarski(A_185),B_186) = k1_xboole_0
      | ~ r2_hidden(A_185,B_186) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_594,c_2129])).

tff(c_38,plain,(
    ! [A_28,B_29] : k2_xboole_0(A_28,k4_xboole_0(B_29,A_28)) = k2_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2249,plain,(
    ! [B_186,A_185] :
      ( k2_xboole_0(B_186,k1_tarski(A_185)) = k2_xboole_0(B_186,k1_xboole_0)
      | ~ r2_hidden(A_185,B_186) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2200,c_38])).

tff(c_2296,plain,(
    ! [B_187,A_188] :
      ( k2_xboole_0(B_187,k1_tarski(A_188)) = B_187
      | ~ r2_hidden(A_188,B_187) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2249])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_62,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_66,plain,(
    k2_xboole_0('#skF_5',k1_tarski('#skF_4')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_62])).

tff(c_2359,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2296,c_66])).

tff(c_2406,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2359])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:50:55 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.59/1.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/1.77  
% 3.59/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/1.77  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 3.59/1.77  
% 3.59/1.77  %Foreground sorts:
% 3.59/1.77  
% 3.59/1.77  
% 3.59/1.77  %Background operators:
% 3.59/1.77  
% 3.59/1.77  
% 3.59/1.77  %Foreground operators:
% 3.59/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.59/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.59/1.77  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.59/1.77  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.59/1.77  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.59/1.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.59/1.77  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.59/1.77  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.59/1.77  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.59/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.59/1.77  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.59/1.77  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.59/1.77  tff('#skF_5', type, '#skF_5': $i).
% 3.59/1.77  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.59/1.77  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.59/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.59/1.77  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.59/1.77  tff('#skF_4', type, '#skF_4': $i).
% 3.59/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.59/1.77  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.59/1.77  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.59/1.77  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.59/1.77  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.59/1.77  
% 4.01/1.78  tff(f_108, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 4.01/1.78  tff(f_75, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 4.01/1.78  tff(f_43, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.01/1.78  tff(f_65, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.01/1.78  tff(f_35, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.01/1.78  tff(f_87, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.01/1.78  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.01/1.78  tff(f_83, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 4.01/1.78  tff(f_71, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.01/1.78  tff(f_79, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.01/1.78  tff(f_73, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.01/1.78  tff(f_101, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.01/1.78  tff(f_81, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.01/1.78  tff(c_64, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.01/1.78  tff(c_34, plain, (![A_25]: (k2_xboole_0(A_25, k1_xboole_0)=A_25)), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.01/1.78  tff(c_16, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.01/1.78  tff(c_380, plain, (![A_93, B_94]: (r2_hidden('#skF_3'(A_93, B_94), A_93) | r1_xboole_0(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.01/1.78  tff(c_6, plain, (![B_8, A_5]: (~r2_hidden(B_8, A_5) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.01/1.78  tff(c_385, plain, (![A_95, B_96]: (~v1_xboole_0(A_95) | r1_xboole_0(A_95, B_96))), inference(resolution, [status(thm)], [c_380, c_6])).
% 4.01/1.78  tff(c_42, plain, (![A_32, B_33]: (k4_xboole_0(A_32, B_33)=A_32 | ~r1_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.01/1.78  tff(c_526, plain, (![A_108, B_109]: (k4_xboole_0(A_108, B_109)=A_108 | ~v1_xboole_0(A_108))), inference(resolution, [status(thm)], [c_385, c_42])).
% 4.01/1.78  tff(c_529, plain, (![B_109]: (k4_xboole_0(k1_xboole_0, B_109)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_526])).
% 4.01/1.78  tff(c_97, plain, (![B_58, A_59]: (k2_xboole_0(B_58, A_59)=k2_xboole_0(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.01/1.78  tff(c_113, plain, (![A_59]: (k2_xboole_0(k1_xboole_0, A_59)=A_59)), inference(superposition, [status(thm), theory('equality')], [c_97, c_34])).
% 4.01/1.78  tff(c_551, plain, (![A_111, B_112]: (k4_xboole_0(k2_xboole_0(A_111, B_112), B_112)=k4_xboole_0(A_111, B_112))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.01/1.78  tff(c_577, plain, (![A_59]: (k4_xboole_0(k1_xboole_0, A_59)=k4_xboole_0(A_59, A_59))), inference(superposition, [status(thm), theory('equality')], [c_113, c_551])).
% 4.01/1.78  tff(c_592, plain, (![A_59]: (k4_xboole_0(A_59, A_59)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_529, c_577])).
% 4.01/1.78  tff(c_30, plain, (![B_22]: (r1_tarski(B_22, B_22))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.01/1.78  tff(c_221, plain, (![A_65, B_66]: (k3_xboole_0(A_65, B_66)=A_65 | ~r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.01/1.78  tff(c_225, plain, (![B_22]: (k3_xboole_0(B_22, B_22)=B_22)), inference(resolution, [status(thm)], [c_30, c_221])).
% 4.01/1.78  tff(c_324, plain, (![A_85, B_86]: (k5_xboole_0(A_85, k3_xboole_0(A_85, B_86))=k4_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.01/1.78  tff(c_333, plain, (![B_22]: (k5_xboole_0(B_22, B_22)=k4_xboole_0(B_22, B_22))), inference(superposition, [status(thm), theory('equality')], [c_225, c_324])).
% 4.01/1.78  tff(c_594, plain, (![B_22]: (k5_xboole_0(B_22, B_22)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_592, c_333])).
% 4.01/1.78  tff(c_287, plain, (![A_78, B_79]: (r1_tarski(k1_tarski(A_78), B_79) | ~r2_hidden(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.01/1.78  tff(c_36, plain, (![A_26, B_27]: (k3_xboole_0(A_26, B_27)=A_26 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.01/1.78  tff(c_2116, plain, (![A_182, B_183]: (k3_xboole_0(k1_tarski(A_182), B_183)=k1_tarski(A_182) | ~r2_hidden(A_182, B_183))), inference(resolution, [status(thm)], [c_287, c_36])).
% 4.01/1.78  tff(c_32, plain, (![A_23, B_24]: (k5_xboole_0(A_23, k3_xboole_0(A_23, B_24))=k4_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.01/1.78  tff(c_2129, plain, (![A_182, B_183]: (k5_xboole_0(k1_tarski(A_182), k1_tarski(A_182))=k4_xboole_0(k1_tarski(A_182), B_183) | ~r2_hidden(A_182, B_183))), inference(superposition, [status(thm), theory('equality')], [c_2116, c_32])).
% 4.01/1.78  tff(c_2200, plain, (![A_185, B_186]: (k4_xboole_0(k1_tarski(A_185), B_186)=k1_xboole_0 | ~r2_hidden(A_185, B_186))), inference(demodulation, [status(thm), theory('equality')], [c_594, c_2129])).
% 4.01/1.78  tff(c_38, plain, (![A_28, B_29]: (k2_xboole_0(A_28, k4_xboole_0(B_29, A_28))=k2_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.01/1.78  tff(c_2249, plain, (![B_186, A_185]: (k2_xboole_0(B_186, k1_tarski(A_185))=k2_xboole_0(B_186, k1_xboole_0) | ~r2_hidden(A_185, B_186))), inference(superposition, [status(thm), theory('equality')], [c_2200, c_38])).
% 4.01/1.78  tff(c_2296, plain, (![B_187, A_188]: (k2_xboole_0(B_187, k1_tarski(A_188))=B_187 | ~r2_hidden(A_188, B_187))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2249])).
% 4.01/1.78  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.01/1.78  tff(c_62, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.01/1.78  tff(c_66, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_62])).
% 4.01/1.78  tff(c_2359, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2296, c_66])).
% 4.01/1.78  tff(c_2406, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_2359])).
% 4.01/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.01/1.78  
% 4.01/1.78  Inference rules
% 4.01/1.78  ----------------------
% 4.01/1.78  #Ref     : 0
% 4.01/1.78  #Sup     : 560
% 4.01/1.78  #Fact    : 0
% 4.01/1.78  #Define  : 0
% 4.01/1.78  #Split   : 1
% 4.01/1.78  #Chain   : 0
% 4.01/1.78  #Close   : 0
% 4.01/1.78  
% 4.01/1.78  Ordering : KBO
% 4.01/1.78  
% 4.01/1.78  Simplification rules
% 4.01/1.78  ----------------------
% 4.01/1.78  #Subsume      : 40
% 4.01/1.78  #Demod        : 473
% 4.01/1.78  #Tautology    : 392
% 4.01/1.78  #SimpNegUnit  : 0
% 4.01/1.78  #BackRed      : 2
% 4.01/1.78  
% 4.01/1.78  #Partial instantiations: 0
% 4.01/1.78  #Strategies tried      : 1
% 4.01/1.78  
% 4.01/1.78  Timing (in seconds)
% 4.01/1.78  ----------------------
% 4.01/1.78  Preprocessing        : 0.36
% 4.01/1.78  Parsing              : 0.16
% 4.01/1.78  CNF conversion       : 0.03
% 4.01/1.78  Main loop            : 0.57
% 4.01/1.79  Inferencing          : 0.19
% 4.01/1.79  Reduction            : 0.23
% 4.01/1.79  Demodulation         : 0.18
% 4.01/1.79  BG Simplification    : 0.04
% 4.01/1.79  Subsumption          : 0.09
% 4.01/1.79  Abstraction          : 0.04
% 4.01/1.79  MUC search           : 0.00
% 4.01/1.79  Cooper               : 0.00
% 4.01/1.79  Total                : 0.97
% 4.01/1.79  Index Insertion      : 0.00
% 4.01/1.79  Index Deletion       : 0.00
% 4.01/1.79  Index Matching       : 0.00
% 4.01/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
