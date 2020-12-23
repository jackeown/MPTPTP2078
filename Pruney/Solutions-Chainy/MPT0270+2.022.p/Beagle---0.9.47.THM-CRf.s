%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:55 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 114 expanded)
%              Number of leaves         :   30 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :   70 ( 118 expanded)
%              Number of equality atoms :   45 (  77 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_46,plain,
    ( ~ r2_hidden('#skF_1','#skF_2')
    | r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_95,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_293,plain,(
    ! [A_69,B_70] :
      ( r1_xboole_0(k1_tarski(A_69),B_70)
      | r2_hidden(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = A_13
      | ~ r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_528,plain,(
    ! [A_88,B_89] :
      ( k4_xboole_0(k1_tarski(A_88),B_89) = k1_tarski(A_88)
      | r2_hidden(A_88,B_89) ) ),
    inference(resolution,[status(thm)],[c_293,c_16])).

tff(c_44,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1')
    | r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_187,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_553,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_528,c_187])).

tff(c_580,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_553])).

tff(c_581,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_14,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_726,plain,(
    ! [A_103,B_104] : k5_xboole_0(A_103,k3_xboole_0(A_103,B_104)) = k4_xboole_0(A_103,B_104) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_755,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = k4_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_726])).

tff(c_762,plain,(
    ! [A_105] : k4_xboole_0(A_105,k1_xboole_0) = A_105 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_755])).

tff(c_12,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_768,plain,(
    ! [A_105] : k4_xboole_0(A_105,A_105) = k3_xboole_0(A_105,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_762,c_12])).

tff(c_773,plain,(
    ! [A_105] : k4_xboole_0(A_105,A_105) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_768])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_582,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_tarski('#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_48,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1')
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_677,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_582,c_48])).

tff(c_703,plain,(
    ! [A_101,B_102] : k4_xboole_0(A_101,k4_xboole_0(A_101,B_102)) = k3_xboole_0(A_101,B_102) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_718,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k3_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_677,c_703])).

tff(c_724,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k3_xboole_0('#skF_4',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_718])).

tff(c_822,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_773,c_724])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_859,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_3')) = k5_xboole_0('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_822,c_8])).

tff(c_862,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_859])).

tff(c_40,plain,(
    ! [C_50,B_49] : ~ r2_hidden(C_50,k4_xboole_0(B_49,k1_tarski(C_50))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_879,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_862,c_40])).

tff(c_885,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_581,c_879])).

tff(c_886,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1115,plain,(
    ! [A_130,B_131] : k5_xboole_0(A_130,k3_xboole_0(A_130,B_131)) = k4_xboole_0(A_130,B_131) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1144,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = k4_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1115])).

tff(c_1151,plain,(
    ! [A_132] : k4_xboole_0(A_132,k1_xboole_0) = A_132 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1144])).

tff(c_1157,plain,(
    ! [A_132] : k4_xboole_0(A_132,A_132) = k3_xboole_0(A_132,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1151,c_12])).

tff(c_1162,plain,(
    ! [A_132] : k4_xboole_0(A_132,A_132) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1157])).

tff(c_887,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_50,plain,
    ( ~ r2_hidden('#skF_1','#skF_2')
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1069,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_887,c_50])).

tff(c_1096,plain,(
    ! [A_128,B_129] : k4_xboole_0(A_128,k4_xboole_0(A_128,B_129)) = k3_xboole_0(A_128,B_129) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1111,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k3_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1069,c_1096])).

tff(c_1114,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k3_xboole_0('#skF_4',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1111])).

tff(c_1322,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1162,c_1114])).

tff(c_1329,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_3')) = k5_xboole_0('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1322,c_8])).

tff(c_1333,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1329])).

tff(c_1344,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1333,c_40])).

tff(c_1350,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_886,c_1344])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:54:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.36  
% 2.54/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.36  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.54/1.36  
% 2.54/1.36  %Foreground sorts:
% 2.54/1.36  
% 2.54/1.36  
% 2.54/1.36  %Background operators:
% 2.54/1.36  
% 2.54/1.36  
% 2.54/1.36  %Foreground operators:
% 2.54/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.54/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.54/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.54/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.54/1.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.54/1.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.54/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.54/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.54/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.54/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.54/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.54/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.54/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.54/1.36  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.54/1.36  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.54/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.54/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.54/1.36  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.54/1.36  
% 2.87/1.38  tff(f_77, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 2.87/1.38  tff(f_64, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.87/1.38  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.87/1.38  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.87/1.38  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.87/1.38  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.87/1.38  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.87/1.38  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.87/1.38  tff(f_71, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.87/1.38  tff(c_46, plain, (~r2_hidden('#skF_1', '#skF_2') | r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.87/1.38  tff(c_95, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_46])).
% 2.87/1.38  tff(c_293, plain, (![A_69, B_70]: (r1_xboole_0(k1_tarski(A_69), B_70) | r2_hidden(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.87/1.38  tff(c_16, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=A_13 | ~r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.87/1.38  tff(c_528, plain, (![A_88, B_89]: (k4_xboole_0(k1_tarski(A_88), B_89)=k1_tarski(A_88) | r2_hidden(A_88, B_89))), inference(resolution, [status(thm)], [c_293, c_16])).
% 2.87/1.38  tff(c_44, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1') | r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.87/1.38  tff(c_187, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 2.87/1.38  tff(c_553, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_528, c_187])).
% 2.87/1.38  tff(c_580, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_553])).
% 2.87/1.38  tff(c_581, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_44])).
% 2.87/1.38  tff(c_14, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.87/1.38  tff(c_10, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.87/1.38  tff(c_726, plain, (![A_103, B_104]: (k5_xboole_0(A_103, k3_xboole_0(A_103, B_104))=k4_xboole_0(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.87/1.38  tff(c_755, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=k4_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_726])).
% 2.87/1.38  tff(c_762, plain, (![A_105]: (k4_xboole_0(A_105, k1_xboole_0)=A_105)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_755])).
% 2.87/1.38  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.87/1.38  tff(c_768, plain, (![A_105]: (k4_xboole_0(A_105, A_105)=k3_xboole_0(A_105, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_762, c_12])).
% 2.87/1.38  tff(c_773, plain, (![A_105]: (k4_xboole_0(A_105, A_105)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_768])).
% 2.87/1.38  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.87/1.38  tff(c_582, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_tarski('#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 2.87/1.38  tff(c_48, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1') | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.87/1.38  tff(c_677, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_582, c_48])).
% 2.87/1.38  tff(c_703, plain, (![A_101, B_102]: (k4_xboole_0(A_101, k4_xboole_0(A_101, B_102))=k3_xboole_0(A_101, B_102))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.87/1.38  tff(c_718, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k3_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_677, c_703])).
% 2.87/1.38  tff(c_724, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k3_xboole_0('#skF_4', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_718])).
% 2.87/1.38  tff(c_822, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_773, c_724])).
% 2.87/1.38  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.87/1.38  tff(c_859, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_3'))=k5_xboole_0('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_822, c_8])).
% 2.87/1.38  tff(c_862, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_859])).
% 2.87/1.38  tff(c_40, plain, (![C_50, B_49]: (~r2_hidden(C_50, k4_xboole_0(B_49, k1_tarski(C_50))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.87/1.38  tff(c_879, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_862, c_40])).
% 2.87/1.38  tff(c_885, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_581, c_879])).
% 2.87/1.38  tff(c_886, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_46])).
% 2.87/1.38  tff(c_1115, plain, (![A_130, B_131]: (k5_xboole_0(A_130, k3_xboole_0(A_130, B_131))=k4_xboole_0(A_130, B_131))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.87/1.38  tff(c_1144, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=k4_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1115])).
% 2.87/1.38  tff(c_1151, plain, (![A_132]: (k4_xboole_0(A_132, k1_xboole_0)=A_132)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1144])).
% 2.87/1.38  tff(c_1157, plain, (![A_132]: (k4_xboole_0(A_132, A_132)=k3_xboole_0(A_132, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1151, c_12])).
% 2.87/1.38  tff(c_1162, plain, (![A_132]: (k4_xboole_0(A_132, A_132)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1157])).
% 2.87/1.38  tff(c_887, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 2.87/1.38  tff(c_50, plain, (~r2_hidden('#skF_1', '#skF_2') | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.87/1.38  tff(c_1069, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_887, c_50])).
% 2.87/1.38  tff(c_1096, plain, (![A_128, B_129]: (k4_xboole_0(A_128, k4_xboole_0(A_128, B_129))=k3_xboole_0(A_128, B_129))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.87/1.38  tff(c_1111, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k3_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1069, c_1096])).
% 2.87/1.38  tff(c_1114, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k3_xboole_0('#skF_4', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1111])).
% 2.87/1.38  tff(c_1322, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1162, c_1114])).
% 2.87/1.38  tff(c_1329, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_3'))=k5_xboole_0('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1322, c_8])).
% 2.87/1.38  tff(c_1333, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1329])).
% 2.87/1.38  tff(c_1344, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1333, c_40])).
% 2.87/1.38  tff(c_1350, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_886, c_1344])).
% 2.87/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.38  
% 2.87/1.38  Inference rules
% 2.87/1.38  ----------------------
% 2.87/1.38  #Ref     : 0
% 2.87/1.38  #Sup     : 305
% 2.87/1.38  #Fact    : 0
% 2.87/1.38  #Define  : 0
% 2.87/1.38  #Split   : 2
% 2.87/1.38  #Chain   : 0
% 2.87/1.38  #Close   : 0
% 2.87/1.38  
% 2.87/1.38  Ordering : KBO
% 2.87/1.38  
% 2.87/1.38  Simplification rules
% 2.87/1.38  ----------------------
% 2.87/1.38  #Subsume      : 10
% 2.87/1.38  #Demod        : 134
% 2.87/1.38  #Tautology    : 250
% 2.87/1.38  #SimpNegUnit  : 4
% 2.87/1.38  #BackRed      : 1
% 2.87/1.38  
% 2.87/1.38  #Partial instantiations: 0
% 2.87/1.38  #Strategies tried      : 1
% 2.87/1.38  
% 2.87/1.38  Timing (in seconds)
% 2.87/1.38  ----------------------
% 2.87/1.38  Preprocessing        : 0.30
% 2.87/1.38  Parsing              : 0.16
% 2.87/1.38  CNF conversion       : 0.02
% 2.87/1.38  Main loop            : 0.33
% 2.87/1.38  Inferencing          : 0.12
% 2.87/1.38  Reduction            : 0.11
% 2.87/1.38  Demodulation         : 0.09
% 2.87/1.38  BG Simplification    : 0.02
% 2.87/1.38  Subsumption          : 0.05
% 2.87/1.38  Abstraction          : 0.02
% 2.87/1.38  MUC search           : 0.00
% 2.87/1.38  Cooper               : 0.00
% 2.87/1.38  Total                : 0.67
% 2.87/1.38  Index Insertion      : 0.00
% 2.87/1.38  Index Deletion       : 0.00
% 2.87/1.38  Index Matching       : 0.00
% 2.87/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
