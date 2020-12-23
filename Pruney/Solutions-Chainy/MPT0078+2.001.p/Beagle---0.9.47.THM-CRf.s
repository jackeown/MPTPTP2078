%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:39 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 155 expanded)
%              Number of leaves         :   20 (  61 expanded)
%              Depth                    :   12
%              Number of atoms          :   50 ( 185 expanded)
%              Number of equality atoms :   39 ( 143 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,B)
          & r1_xboole_0(A,B)
          & r1_xboole_0(C,B) )
       => A = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_24,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_18,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_26,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_173,plain,(
    ! [A_29,B_30] :
      ( k3_xboole_0(A_29,B_30) = k1_xboole_0
      | ~ r1_xboole_0(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_180,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_173])).

tff(c_20,plain,(
    ! [A_13,B_14] : k4_xboole_0(k2_xboole_0(A_13,B_14),B_14) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_30,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_303,plain,(
    ! [A_40,B_41] : k4_xboole_0(k2_xboole_0(A_40,B_41),B_41) = k4_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_328,plain,(
    k4_xboole_0(k2_xboole_0('#skF_1','#skF_2'),'#skF_2') = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_303])).

tff(c_336,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_328])).

tff(c_22,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_461,plain,(
    k4_xboole_0('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_22])).

tff(c_470,plain,(
    k4_xboole_0('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_461])).

tff(c_649,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k4_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_470,c_22])).

tff(c_659,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_649])).

tff(c_16,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_195,plain,(
    ! [A_33,B_34] :
      ( k4_xboole_0(A_33,B_34) = k1_xboole_0
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_207,plain,(
    ! [A_10,B_11] : k4_xboole_0(k4_xboole_0(A_10,B_11),A_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_195])).

tff(c_338,plain,(
    ! [A_42,B_43] : k4_xboole_0(A_42,k4_xboole_0(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_366,plain,(
    ! [A_10,B_11] : k4_xboole_0(k4_xboole_0(A_10,B_11),k1_xboole_0) = k3_xboole_0(k4_xboole_0(A_10,B_11),A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_338])).

tff(c_1081,plain,(
    ! [A_63,B_64] : k3_xboole_0(k4_xboole_0(A_63,B_64),A_63) = k4_xboole_0(A_63,B_64) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_366])).

tff(c_1133,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_3') = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_1081])).

tff(c_1178,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_3') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_1133])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1365,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1178,c_4])).

tff(c_1381,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_659,c_1365])).

tff(c_28,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_181,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_173])).

tff(c_1431,plain,(
    ! [A_67,B_68] : k4_xboole_0(A_67,k3_xboole_0(A_67,B_68)) = k3_xboole_0(A_67,k4_xboole_0(A_67,B_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_338])).

tff(c_1478,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_1','#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_1431])).

tff(c_1505,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1381,c_18,c_1478])).

tff(c_1420,plain,(
    k4_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1381,c_207])).

tff(c_1634,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k3_xboole_0('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1420,c_22])).

tff(c_1648,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1505,c_4,c_18,c_1634])).

tff(c_1650,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_1648])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:20:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.38/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.60  
% 3.38/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.61  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.38/1.61  
% 3.38/1.61  %Foreground sorts:
% 3.38/1.61  
% 3.38/1.61  
% 3.38/1.61  %Background operators:
% 3.38/1.61  
% 3.38/1.61  
% 3.38/1.61  %Foreground operators:
% 3.38/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.38/1.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.38/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.38/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.38/1.61  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.38/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.38/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.38/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.38/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.38/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.38/1.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.38/1.61  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.38/1.61  
% 3.38/1.62  tff(f_56, negated_conjecture, ~(![A, B, C]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, B)) & r1_xboole_0(A, B)) & r1_xboole_0(C, B)) => (A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_xboole_1)).
% 3.38/1.62  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.38/1.62  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.38/1.62  tff(f_45, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 3.38/1.62  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.38/1.62  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.38/1.62  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.38/1.62  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.38/1.62  tff(c_24, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.38/1.62  tff(c_18, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.38/1.62  tff(c_26, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.38/1.62  tff(c_173, plain, (![A_29, B_30]: (k3_xboole_0(A_29, B_30)=k1_xboole_0 | ~r1_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.38/1.62  tff(c_180, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_173])).
% 3.38/1.62  tff(c_20, plain, (![A_13, B_14]: (k4_xboole_0(k2_xboole_0(A_13, B_14), B_14)=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.38/1.62  tff(c_30, plain, (k2_xboole_0('#skF_3', '#skF_2')=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.38/1.62  tff(c_303, plain, (![A_40, B_41]: (k4_xboole_0(k2_xboole_0(A_40, B_41), B_41)=k4_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.38/1.62  tff(c_328, plain, (k4_xboole_0(k2_xboole_0('#skF_1', '#skF_2'), '#skF_2')=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_30, c_303])).
% 3.38/1.62  tff(c_336, plain, (k4_xboole_0('#skF_3', '#skF_2')=k4_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_328])).
% 3.38/1.62  tff(c_22, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.38/1.62  tff(c_461, plain, (k4_xboole_0('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_336, c_22])).
% 3.38/1.62  tff(c_470, plain, (k4_xboole_0('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_180, c_461])).
% 3.38/1.62  tff(c_649, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k4_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_470, c_22])).
% 3.38/1.62  tff(c_659, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_649])).
% 3.38/1.62  tff(c_16, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.38/1.62  tff(c_195, plain, (![A_33, B_34]: (k4_xboole_0(A_33, B_34)=k1_xboole_0 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.38/1.62  tff(c_207, plain, (![A_10, B_11]: (k4_xboole_0(k4_xboole_0(A_10, B_11), A_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_195])).
% 3.38/1.62  tff(c_338, plain, (![A_42, B_43]: (k4_xboole_0(A_42, k4_xboole_0(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.38/1.62  tff(c_366, plain, (![A_10, B_11]: (k4_xboole_0(k4_xboole_0(A_10, B_11), k1_xboole_0)=k3_xboole_0(k4_xboole_0(A_10, B_11), A_10))), inference(superposition, [status(thm), theory('equality')], [c_207, c_338])).
% 3.38/1.62  tff(c_1081, plain, (![A_63, B_64]: (k3_xboole_0(k4_xboole_0(A_63, B_64), A_63)=k4_xboole_0(A_63, B_64))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_366])).
% 3.38/1.62  tff(c_1133, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3')=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_336, c_1081])).
% 3.38/1.62  tff(c_1178, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3')=k4_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_336, c_1133])).
% 3.38/1.62  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.38/1.62  tff(c_1365, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1178, c_4])).
% 3.38/1.62  tff(c_1381, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_659, c_1365])).
% 3.38/1.62  tff(c_28, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.38/1.62  tff(c_181, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_173])).
% 3.38/1.62  tff(c_1431, plain, (![A_67, B_68]: (k4_xboole_0(A_67, k3_xboole_0(A_67, B_68))=k3_xboole_0(A_67, k4_xboole_0(A_67, B_68)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_338])).
% 3.38/1.62  tff(c_1478, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_1', '#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_181, c_1431])).
% 3.38/1.62  tff(c_1505, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1381, c_18, c_1478])).
% 3.38/1.62  tff(c_1420, plain, (k4_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1381, c_207])).
% 3.38/1.62  tff(c_1634, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k3_xboole_0('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1420, c_22])).
% 3.38/1.62  tff(c_1648, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1505, c_4, c_18, c_1634])).
% 3.38/1.62  tff(c_1650, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_1648])).
% 3.38/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.62  
% 3.38/1.62  Inference rules
% 3.38/1.62  ----------------------
% 3.38/1.62  #Ref     : 0
% 3.38/1.62  #Sup     : 413
% 3.38/1.62  #Fact    : 0
% 3.38/1.62  #Define  : 0
% 3.38/1.62  #Split   : 0
% 3.38/1.62  #Chain   : 0
% 3.38/1.62  #Close   : 0
% 3.38/1.62  
% 3.38/1.62  Ordering : KBO
% 3.38/1.62  
% 3.38/1.62  Simplification rules
% 3.38/1.62  ----------------------
% 3.38/1.62  #Subsume      : 0
% 3.38/1.62  #Demod        : 358
% 3.38/1.62  #Tautology    : 318
% 3.38/1.62  #SimpNegUnit  : 1
% 3.38/1.62  #BackRed      : 7
% 3.38/1.62  
% 3.38/1.62  #Partial instantiations: 0
% 3.38/1.62  #Strategies tried      : 1
% 3.38/1.62  
% 3.38/1.62  Timing (in seconds)
% 3.38/1.62  ----------------------
% 3.38/1.62  Preprocessing        : 0.29
% 3.38/1.62  Parsing              : 0.16
% 3.38/1.62  CNF conversion       : 0.02
% 3.38/1.62  Main loop            : 0.56
% 3.38/1.62  Inferencing          : 0.18
% 3.38/1.62  Reduction            : 0.25
% 3.38/1.62  Demodulation         : 0.20
% 3.38/1.62  BG Simplification    : 0.02
% 3.38/1.62  Subsumption          : 0.08
% 3.38/1.62  Abstraction          : 0.02
% 3.38/1.62  MUC search           : 0.00
% 3.38/1.62  Cooper               : 0.00
% 3.38/1.62  Total                : 0.88
% 3.38/1.62  Index Insertion      : 0.00
% 3.38/1.63  Index Deletion       : 0.00
% 3.38/1.63  Index Matching       : 0.00
% 3.38/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
