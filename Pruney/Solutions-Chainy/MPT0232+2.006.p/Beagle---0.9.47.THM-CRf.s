%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:20 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 110 expanded)
%              Number of leaves         :   33 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :   60 ( 137 expanded)
%              Number of equality atoms :   26 (  64 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_84,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_152,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => k2_tarski(A,B) = k1_tarski(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_zfmisc_1)).

tff(f_147,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_112,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_110,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_90,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_98,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_136,axiom,(
    ! [A,B] :
      ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
     => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l20_zfmisc_1)).

tff(f_141,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(c_36,plain,(
    ! [A_37] : r1_tarski(k1_xboole_0,A_37) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_90,plain,(
    k2_tarski('#skF_2','#skF_3') != k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_92,plain,(
    r1_tarski(k2_tarski('#skF_2','#skF_3'),k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1851,plain,(
    ! [B_187,A_188] :
      ( k1_tarski(B_187) = A_188
      | k1_xboole_0 = A_188
      | ~ r1_tarski(A_188,k1_tarski(B_187)) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_1874,plain,
    ( k2_tarski('#skF_2','#skF_3') = k1_tarski('#skF_4')
    | k2_tarski('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_92,c_1851])).

tff(c_1898,plain,(
    k2_tarski('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_1874])).

tff(c_1452,plain,(
    ! [A_166,B_167] : k2_xboole_0(k1_tarski(A_166),k1_tarski(B_167)) = k2_tarski(A_166,B_167) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_168,plain,(
    ! [B_111,A_112] : k2_xboole_0(B_111,A_112) = k2_xboole_0(A_112,B_111) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_54,plain,(
    ! [A_54,B_55] : r1_tarski(A_54,k2_xboole_0(A_54,B_55)) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_183,plain,(
    ! [A_112,B_111] : r1_tarski(A_112,k2_xboole_0(B_111,A_112)) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_54])).

tff(c_1473,plain,(
    ! [B_167,A_166] : r1_tarski(k1_tarski(B_167),k2_tarski(A_166,B_167)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1452,c_183])).

tff(c_1927,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1898,c_1473])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( B_6 = A_5
      | ~ r1_tarski(B_6,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2007,plain,
    ( k1_tarski('#skF_3') = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1927,c_6])).

tff(c_2025,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2007])).

tff(c_146,plain,(
    ! [A_106,B_107] : r1_tarski(k4_xboole_0(A_106,B_107),A_106) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_46,plain,(
    ! [A_45] :
      ( k1_xboole_0 = A_45
      | ~ r1_tarski(A_45,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_151,plain,(
    ! [B_107] : k4_xboole_0(k1_xboole_0,B_107) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_146,c_46])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_406,plain,(
    ! [A_126,B_127] :
      ( k2_xboole_0(A_126,B_127) = B_127
      | ~ r1_tarski(A_126,B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_435,plain,(
    ! [A_37] : k2_xboole_0(k1_xboole_0,A_37) = A_37 ),
    inference(resolution,[status(thm)],[c_36,c_406])).

tff(c_2066,plain,(
    ! [A_189,B_190] :
      ( r2_hidden(A_189,B_190)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(A_189),B_190),B_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_2069,plain,(
    ! [B_190] :
      ( r2_hidden('#skF_3',B_190)
      | ~ r1_tarski(k2_xboole_0(k1_xboole_0,B_190),B_190) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2025,c_2066])).

tff(c_2117,plain,(
    ! [B_190] : r2_hidden('#skF_3',B_190) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_435,c_2069])).

tff(c_2428,plain,(
    ! [A_200,B_201] :
      ( ~ r2_hidden(A_200,B_201)
      | k4_xboole_0(k1_tarski(A_200),B_201) != k1_tarski(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_2434,plain,(
    ! [B_201] :
      ( ~ r2_hidden('#skF_3',B_201)
      | k4_xboole_0(k1_xboole_0,B_201) != k1_tarski('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2025,c_2428])).

tff(c_2459,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2025,c_151,c_2117,c_2434])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:43:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.53/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.61  
% 3.53/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.61  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.53/1.61  
% 3.53/1.61  %Foreground sorts:
% 3.53/1.61  
% 3.53/1.61  
% 3.53/1.61  %Background operators:
% 3.53/1.61  
% 3.53/1.61  
% 3.53/1.61  %Foreground operators:
% 3.53/1.61  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.53/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.53/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.53/1.61  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.53/1.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.53/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.53/1.61  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.53/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.53/1.61  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.53/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.53/1.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.53/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.53/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.53/1.61  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.53/1.61  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.53/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.53/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.53/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.53/1.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.53/1.61  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.53/1.61  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.53/1.61  
% 3.53/1.62  tff(f_84, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.53/1.62  tff(f_152, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (k2_tarski(A, B) = k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_zfmisc_1)).
% 3.53/1.62  tff(f_147, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.53/1.62  tff(f_112, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 3.53/1.62  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.53/1.62  tff(f_110, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.53/1.62  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.53/1.62  tff(f_90, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.53/1.62  tff(f_98, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.53/1.62  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.53/1.62  tff(f_136, axiom, (![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l20_zfmisc_1)).
% 3.53/1.62  tff(f_141, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 3.53/1.62  tff(c_36, plain, (![A_37]: (r1_tarski(k1_xboole_0, A_37))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.53/1.62  tff(c_90, plain, (k2_tarski('#skF_2', '#skF_3')!=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.53/1.62  tff(c_92, plain, (r1_tarski(k2_tarski('#skF_2', '#skF_3'), k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.53/1.62  tff(c_1851, plain, (![B_187, A_188]: (k1_tarski(B_187)=A_188 | k1_xboole_0=A_188 | ~r1_tarski(A_188, k1_tarski(B_187)))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.53/1.62  tff(c_1874, plain, (k2_tarski('#skF_2', '#skF_3')=k1_tarski('#skF_4') | k2_tarski('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_92, c_1851])).
% 3.53/1.62  tff(c_1898, plain, (k2_tarski('#skF_2', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_90, c_1874])).
% 3.53/1.62  tff(c_1452, plain, (![A_166, B_167]: (k2_xboole_0(k1_tarski(A_166), k1_tarski(B_167))=k2_tarski(A_166, B_167))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.53/1.62  tff(c_168, plain, (![B_111, A_112]: (k2_xboole_0(B_111, A_112)=k2_xboole_0(A_112, B_111))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.53/1.62  tff(c_54, plain, (![A_54, B_55]: (r1_tarski(A_54, k2_xboole_0(A_54, B_55)))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.53/1.62  tff(c_183, plain, (![A_112, B_111]: (r1_tarski(A_112, k2_xboole_0(B_111, A_112)))), inference(superposition, [status(thm), theory('equality')], [c_168, c_54])).
% 3.53/1.62  tff(c_1473, plain, (![B_167, A_166]: (r1_tarski(k1_tarski(B_167), k2_tarski(A_166, B_167)))), inference(superposition, [status(thm), theory('equality')], [c_1452, c_183])).
% 3.53/1.62  tff(c_1927, plain, (r1_tarski(k1_tarski('#skF_3'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1898, c_1473])).
% 3.53/1.62  tff(c_6, plain, (![B_6, A_5]: (B_6=A_5 | ~r1_tarski(B_6, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.53/1.62  tff(c_2007, plain, (k1_tarski('#skF_3')=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_1927, c_6])).
% 3.53/1.62  tff(c_2025, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2007])).
% 3.53/1.62  tff(c_146, plain, (![A_106, B_107]: (r1_tarski(k4_xboole_0(A_106, B_107), A_106))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.53/1.62  tff(c_46, plain, (![A_45]: (k1_xboole_0=A_45 | ~r1_tarski(A_45, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.53/1.62  tff(c_151, plain, (![B_107]: (k4_xboole_0(k1_xboole_0, B_107)=k1_xboole_0)), inference(resolution, [status(thm)], [c_146, c_46])).
% 3.53/1.62  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.53/1.62  tff(c_406, plain, (![A_126, B_127]: (k2_xboole_0(A_126, B_127)=B_127 | ~r1_tarski(A_126, B_127))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.53/1.62  tff(c_435, plain, (![A_37]: (k2_xboole_0(k1_xboole_0, A_37)=A_37)), inference(resolution, [status(thm)], [c_36, c_406])).
% 3.53/1.62  tff(c_2066, plain, (![A_189, B_190]: (r2_hidden(A_189, B_190) | ~r1_tarski(k2_xboole_0(k1_tarski(A_189), B_190), B_190))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.53/1.62  tff(c_2069, plain, (![B_190]: (r2_hidden('#skF_3', B_190) | ~r1_tarski(k2_xboole_0(k1_xboole_0, B_190), B_190))), inference(superposition, [status(thm), theory('equality')], [c_2025, c_2066])).
% 3.53/1.62  tff(c_2117, plain, (![B_190]: (r2_hidden('#skF_3', B_190))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_435, c_2069])).
% 3.53/1.62  tff(c_2428, plain, (![A_200, B_201]: (~r2_hidden(A_200, B_201) | k4_xboole_0(k1_tarski(A_200), B_201)!=k1_tarski(A_200))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.53/1.62  tff(c_2434, plain, (![B_201]: (~r2_hidden('#skF_3', B_201) | k4_xboole_0(k1_xboole_0, B_201)!=k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2025, c_2428])).
% 3.53/1.62  tff(c_2459, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2025, c_151, c_2117, c_2434])).
% 3.53/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.62  
% 3.53/1.62  Inference rules
% 3.53/1.62  ----------------------
% 3.53/1.62  #Ref     : 0
% 3.53/1.62  #Sup     : 564
% 3.53/1.62  #Fact    : 0
% 3.53/1.62  #Define  : 0
% 3.53/1.62  #Split   : 0
% 3.53/1.62  #Chain   : 0
% 3.53/1.62  #Close   : 0
% 3.53/1.62  
% 3.53/1.62  Ordering : KBO
% 3.53/1.62  
% 3.53/1.62  Simplification rules
% 3.53/1.62  ----------------------
% 3.53/1.62  #Subsume      : 12
% 3.53/1.62  #Demod        : 386
% 3.53/1.62  #Tautology    : 414
% 3.53/1.62  #SimpNegUnit  : 2
% 3.53/1.62  #BackRed      : 10
% 3.53/1.62  
% 3.53/1.62  #Partial instantiations: 0
% 3.53/1.62  #Strategies tried      : 1
% 3.53/1.62  
% 3.53/1.62  Timing (in seconds)
% 3.53/1.62  ----------------------
% 3.53/1.63  Preprocessing        : 0.37
% 3.53/1.63  Parsing              : 0.19
% 3.53/1.63  CNF conversion       : 0.03
% 3.53/1.63  Main loop            : 0.46
% 3.53/1.63  Inferencing          : 0.14
% 3.53/1.63  Reduction            : 0.18
% 3.53/1.63  Demodulation         : 0.14
% 3.53/1.63  BG Simplification    : 0.03
% 3.53/1.63  Subsumption          : 0.08
% 3.53/1.63  Abstraction          : 0.02
% 3.53/1.63  MUC search           : 0.00
% 3.53/1.63  Cooper               : 0.00
% 3.53/1.63  Total                : 0.85
% 3.53/1.63  Index Insertion      : 0.00
% 3.53/1.63  Index Deletion       : 0.00
% 3.53/1.63  Index Matching       : 0.00
% 3.53/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
