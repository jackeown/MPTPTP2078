%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:09 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   47 (  60 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   43 (  63 expanded)
%              Number of equality atoms :   29 (  40 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_47,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_51,plain,(
    ! [A_26,B_27] :
      ( r1_xboole_0(A_26,B_27)
      | k3_xboole_0(A_26,B_27) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_55,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_51,c_28])).

tff(c_253,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k4_xboole_0(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_56,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_71,plain,(
    ! [A_6,B_7] : k4_xboole_0(k4_xboole_0(A_6,B_7),A_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_56])).

tff(c_510,plain,(
    ! [A_49,B_50] : k4_xboole_0(k3_xboole_0(A_49,B_50),A_49) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_71])).

tff(c_20,plain,(
    ! [A_13,B_14,C_15] : k4_xboole_0(k3_xboole_0(A_13,B_14),C_15) = k3_xboole_0(A_13,k4_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_515,plain,(
    ! [A_49,B_50] : k3_xboole_0(A_49,k4_xboole_0(B_50,A_49)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_510,c_20])).

tff(c_14,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_26,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_72,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_56])).

tff(c_297,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_253])).

tff(c_310,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_297])).

tff(c_643,plain,(
    ! [A_53,B_54,C_55] : k4_xboole_0(k3_xboole_0(A_53,B_54),k3_xboole_0(A_53,C_55)) = k3_xboole_0(A_53,k4_xboole_0(B_54,C_55)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_702,plain,(
    ! [B_54] : k4_xboole_0(k3_xboole_0('#skF_1',B_54),'#skF_1') = k3_xboole_0('#skF_1',k4_xboole_0(B_54,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_643])).

tff(c_731,plain,(
    ! [B_54] : k3_xboole_0('#skF_1',k4_xboole_0(B_54,'#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_515,c_20,c_702])).

tff(c_16,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_24,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_110,plain,(
    ! [A_32,B_33] :
      ( k3_xboole_0(A_32,B_33) = k1_xboole_0
      | ~ r1_xboole_0(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_118,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_110])).

tff(c_708,plain,(
    ! [B_54] : k3_xboole_0('#skF_1',k4_xboole_0(B_54,k3_xboole_0('#skF_2','#skF_3'))) = k4_xboole_0(k3_xboole_0('#skF_1',B_54),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_643])).

tff(c_951,plain,(
    ! [B_60] : k3_xboole_0('#skF_1',k4_xboole_0(B_60,k3_xboole_0('#skF_2','#skF_3'))) = k3_xboole_0('#skF_1',B_60) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_708])).

tff(c_998,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_951])).

tff(c_1018,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_731,c_998])).

tff(c_1020,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_1018])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:24:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.56/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.35  
% 2.56/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.36  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.56/1.36  
% 2.56/1.36  %Foreground sorts:
% 2.56/1.36  
% 2.56/1.36  
% 2.56/1.36  %Background operators:
% 2.56/1.36  
% 2.56/1.36  
% 2.56/1.36  %Foreground operators:
% 2.56/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.56/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.56/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.56/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.56/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.56/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.56/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.56/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.56/1.36  
% 2.56/1.37  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.56/1.37  tff(f_56, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_xboole_1)).
% 2.56/1.37  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.56/1.37  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.56/1.37  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.56/1.37  tff(f_45, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.56/1.37  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.56/1.37  tff(f_47, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_xboole_1)).
% 2.56/1.37  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.56/1.37  tff(c_51, plain, (![A_26, B_27]: (r1_xboole_0(A_26, B_27) | k3_xboole_0(A_26, B_27)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.56/1.37  tff(c_28, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.56/1.37  tff(c_55, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_51, c_28])).
% 2.56/1.37  tff(c_253, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k4_xboole_0(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.56/1.37  tff(c_12, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.56/1.37  tff(c_56, plain, (![A_28, B_29]: (k4_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.56/1.37  tff(c_71, plain, (![A_6, B_7]: (k4_xboole_0(k4_xboole_0(A_6, B_7), A_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_56])).
% 2.56/1.37  tff(c_510, plain, (![A_49, B_50]: (k4_xboole_0(k3_xboole_0(A_49, B_50), A_49)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_253, c_71])).
% 2.56/1.37  tff(c_20, plain, (![A_13, B_14, C_15]: (k4_xboole_0(k3_xboole_0(A_13, B_14), C_15)=k3_xboole_0(A_13, k4_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.56/1.37  tff(c_515, plain, (![A_49, B_50]: (k3_xboole_0(A_49, k4_xboole_0(B_50, A_49))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_510, c_20])).
% 2.56/1.37  tff(c_14, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.56/1.37  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.56/1.37  tff(c_72, plain, (k4_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_56])).
% 2.56/1.37  tff(c_297, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_72, c_253])).
% 2.56/1.37  tff(c_310, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_297])).
% 2.56/1.37  tff(c_643, plain, (![A_53, B_54, C_55]: (k4_xboole_0(k3_xboole_0(A_53, B_54), k3_xboole_0(A_53, C_55))=k3_xboole_0(A_53, k4_xboole_0(B_54, C_55)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.56/1.37  tff(c_702, plain, (![B_54]: (k4_xboole_0(k3_xboole_0('#skF_1', B_54), '#skF_1')=k3_xboole_0('#skF_1', k4_xboole_0(B_54, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_310, c_643])).
% 2.56/1.37  tff(c_731, plain, (![B_54]: (k3_xboole_0('#skF_1', k4_xboole_0(B_54, '#skF_3'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_515, c_20, c_702])).
% 2.56/1.37  tff(c_16, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.56/1.37  tff(c_24, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.56/1.37  tff(c_110, plain, (![A_32, B_33]: (k3_xboole_0(A_32, B_33)=k1_xboole_0 | ~r1_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.56/1.37  tff(c_118, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_110])).
% 2.56/1.37  tff(c_708, plain, (![B_54]: (k3_xboole_0('#skF_1', k4_xboole_0(B_54, k3_xboole_0('#skF_2', '#skF_3')))=k4_xboole_0(k3_xboole_0('#skF_1', B_54), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_118, c_643])).
% 2.56/1.37  tff(c_951, plain, (![B_60]: (k3_xboole_0('#skF_1', k4_xboole_0(B_60, k3_xboole_0('#skF_2', '#skF_3')))=k3_xboole_0('#skF_1', B_60))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_708])).
% 2.56/1.37  tff(c_998, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_16, c_951])).
% 2.56/1.37  tff(c_1018, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_731, c_998])).
% 2.56/1.37  tff(c_1020, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_1018])).
% 2.56/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.37  
% 2.56/1.37  Inference rules
% 2.56/1.37  ----------------------
% 2.56/1.37  #Ref     : 0
% 2.56/1.37  #Sup     : 249
% 2.56/1.37  #Fact    : 0
% 2.56/1.37  #Define  : 0
% 2.56/1.37  #Split   : 0
% 2.56/1.37  #Chain   : 0
% 2.56/1.37  #Close   : 0
% 2.56/1.37  
% 2.56/1.37  Ordering : KBO
% 2.56/1.37  
% 2.56/1.37  Simplification rules
% 2.56/1.37  ----------------------
% 2.56/1.37  #Subsume      : 0
% 2.56/1.37  #Demod        : 167
% 2.56/1.37  #Tautology    : 166
% 2.56/1.37  #SimpNegUnit  : 1
% 2.56/1.37  #BackRed      : 0
% 2.56/1.37  
% 2.56/1.37  #Partial instantiations: 0
% 2.56/1.37  #Strategies tried      : 1
% 2.56/1.37  
% 2.56/1.37  Timing (in seconds)
% 2.56/1.37  ----------------------
% 2.56/1.37  Preprocessing        : 0.28
% 2.56/1.37  Parsing              : 0.15
% 2.56/1.37  CNF conversion       : 0.02
% 2.56/1.37  Main loop            : 0.34
% 2.56/1.37  Inferencing          : 0.13
% 2.56/1.37  Reduction            : 0.13
% 2.56/1.37  Demodulation         : 0.10
% 2.56/1.37  BG Simplification    : 0.02
% 2.56/1.37  Subsumption          : 0.05
% 2.56/1.37  Abstraction          : 0.02
% 2.56/1.37  MUC search           : 0.00
% 2.56/1.37  Cooper               : 0.00
% 2.56/1.37  Total                : 0.64
% 2.56/1.37  Index Insertion      : 0.00
% 2.56/1.37  Index Deletion       : 0.00
% 2.56/1.37  Index Matching       : 0.00
% 2.56/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
