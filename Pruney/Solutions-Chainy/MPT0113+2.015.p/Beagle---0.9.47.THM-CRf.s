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
% DateTime   : Thu Dec  3 09:45:13 EST 2020

% Result     : Theorem 7.08s
% Output     : CNFRefutation 7.08s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 106 expanded)
%              Number of leaves         :   23 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :   64 ( 124 expanded)
%              Number of equality atoms :   40 (  63 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_67,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8140,plain,(
    ! [A_217,B_218] :
      ( r1_xboole_0(A_217,B_218)
      | k3_xboole_0(A_217,B_218) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_310,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(A_57,B_58)
      | k4_xboole_0(A_57,B_58) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_38,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_68,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_318,plain,(
    k4_xboole_0('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_310,c_68])).

tff(c_215,plain,(
    ! [A_43,B_44] : k3_xboole_0(A_43,k2_xboole_0(A_43,B_44)) = A_43 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    ! [A_16,B_17] : r1_tarski(k3_xboole_0(A_16,B_17),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_224,plain,(
    ! [A_43] : r1_tarski(A_43,A_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_22])).

tff(c_233,plain,(
    ! [A_50,B_51] :
      ( k4_xboole_0(A_50,B_51) = k1_xboole_0
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_250,plain,(
    ! [A_43] : k4_xboole_0(A_43,A_43) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_224,c_233])).

tff(c_868,plain,(
    ! [A_89,B_90,C_91] : k4_xboole_0(k3_xboole_0(A_89,B_90),C_91) = k3_xboole_0(A_89,k4_xboole_0(B_90,C_91)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_69,plain,(
    ! [B_36,A_37] : k3_xboole_0(B_36,A_37) = k3_xboole_0(A_37,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_84,plain,(
    ! [B_36,A_37] : r1_tarski(k3_xboole_0(B_36,A_37),A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_22])).

tff(c_251,plain,(
    ! [B_36,A_37] : k4_xboole_0(k3_xboole_0(B_36,A_37),A_37) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_84,c_233])).

tff(c_886,plain,(
    ! [A_89,C_91] : k3_xboole_0(A_89,k4_xboole_0(C_91,C_91)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_868,c_251])).

tff(c_936,plain,(
    ! [A_89] : k3_xboole_0(A_89,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_886])).

tff(c_332,plain,(
    ! [A_63,B_64] :
      ( k3_xboole_0(A_63,B_64) = A_63
      | ~ r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_354,plain,(
    ! [A_43] : k3_xboole_0(A_43,A_43) = A_43 ),
    inference(resolution,[status(thm)],[c_224,c_332])).

tff(c_3248,plain,(
    ! [B_137,A_138,C_139] : k4_xboole_0(k3_xboole_0(B_137,A_138),C_139) = k3_xboole_0(A_138,k4_xboole_0(B_137,C_139)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_868])).

tff(c_7343,plain,(
    ! [A_183,C_184] : k3_xboole_0(A_183,k4_xboole_0(A_183,C_184)) = k4_xboole_0(A_183,C_184) ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_3248])).

tff(c_252,plain,(
    ! [A_16,B_17] : k4_xboole_0(k3_xboole_0(A_16,B_17),A_16) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_233])).

tff(c_7617,plain,(
    ! [A_187,C_188] : k4_xboole_0(k4_xboole_0(A_187,C_188),A_187) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7343,c_252])).

tff(c_40,plain,(
    r1_tarski('#skF_2',k4_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_357,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_3','#skF_4')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_40,c_332])).

tff(c_907,plain,(
    ! [C_91] : k3_xboole_0('#skF_2',k4_xboole_0(k4_xboole_0('#skF_3','#skF_4'),C_91)) = k4_xboole_0('#skF_2',C_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_868])).

tff(c_7673,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k3_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_7617,c_907])).

tff(c_7743,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_936,c_7673])).

tff(c_7745,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_318,c_7743])).

tff(c_7746,plain,(
    ~ r1_xboole_0('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_8146,plain,(
    k3_xboole_0('#skF_2','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8140,c_7746])).

tff(c_8149,plain,(
    k3_xboole_0('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8146])).

tff(c_7747,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_7911,plain,(
    ! [A_201,B_202] :
      ( k3_xboole_0(A_201,B_202) = A_201
      | ~ r1_tarski(A_201,B_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_7934,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_7747,c_7911])).

tff(c_9848,plain,(
    ! [A_265,B_266,C_267] : k4_xboole_0(k3_xboole_0(A_265,B_266),C_267) = k3_xboole_0(A_265,k4_xboole_0(B_266,C_267)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_12227,plain,(
    ! [C_300] : k3_xboole_0('#skF_2',k4_xboole_0('#skF_3',C_300)) = k4_xboole_0('#skF_2',C_300) ),
    inference(superposition,[status(thm),theory(equality)],[c_7934,c_9848])).

tff(c_7936,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_3','#skF_4')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_40,c_7911])).

tff(c_12276,plain,(
    k4_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_12227,c_7936])).

tff(c_7937,plain,(
    ! [A_203,B_204] :
      ( k4_xboole_0(A_203,B_204) = k1_xboole_0
      | ~ r1_tarski(A_203,B_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_7960,plain,(
    ! [A_16,B_17] : k4_xboole_0(k3_xboole_0(A_16,B_17),A_16) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_7937])).

tff(c_9906,plain,(
    ! [A_16,B_17] : k3_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7960,c_9848])).

tff(c_12347,plain,(
    k3_xboole_0('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12276,c_9906])).

tff(c_12370,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8149,c_12347])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:23:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.08/2.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.08/2.76  
% 7.08/2.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.08/2.76  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 7.08/2.76  
% 7.08/2.76  %Foreground sorts:
% 7.08/2.76  
% 7.08/2.76  
% 7.08/2.76  %Background operators:
% 7.08/2.76  
% 7.08/2.76  
% 7.08/2.76  %Foreground operators:
% 7.08/2.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.08/2.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.08/2.76  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.08/2.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.08/2.76  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.08/2.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.08/2.76  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.08/2.76  tff('#skF_2', type, '#skF_2': $i).
% 7.08/2.76  tff('#skF_3', type, '#skF_3': $i).
% 7.08/2.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.08/2.76  tff('#skF_4', type, '#skF_4': $i).
% 7.08/2.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.08/2.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.08/2.76  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.08/2.76  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.08/2.76  
% 7.08/2.77  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.08/2.77  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.08/2.77  tff(f_55, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 7.08/2.77  tff(f_82, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 7.08/2.77  tff(f_61, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 7.08/2.77  tff(f_59, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 7.08/2.77  tff(f_67, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 7.08/2.77  tff(f_65, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.08/2.77  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.08/2.77  tff(c_8140, plain, (![A_217, B_218]: (r1_xboole_0(A_217, B_218) | k3_xboole_0(A_217, B_218)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.08/2.77  tff(c_310, plain, (![A_57, B_58]: (r1_tarski(A_57, B_58) | k4_xboole_0(A_57, B_58)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.08/2.77  tff(c_38, plain, (~r1_xboole_0('#skF_2', '#skF_4') | ~r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.08/2.77  tff(c_68, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_38])).
% 7.08/2.77  tff(c_318, plain, (k4_xboole_0('#skF_2', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_310, c_68])).
% 7.08/2.77  tff(c_215, plain, (![A_43, B_44]: (k3_xboole_0(A_43, k2_xboole_0(A_43, B_44))=A_43)), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.08/2.77  tff(c_22, plain, (![A_16, B_17]: (r1_tarski(k3_xboole_0(A_16, B_17), A_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.08/2.77  tff(c_224, plain, (![A_43]: (r1_tarski(A_43, A_43))), inference(superposition, [status(thm), theory('equality')], [c_215, c_22])).
% 7.08/2.77  tff(c_233, plain, (![A_50, B_51]: (k4_xboole_0(A_50, B_51)=k1_xboole_0 | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.08/2.77  tff(c_250, plain, (![A_43]: (k4_xboole_0(A_43, A_43)=k1_xboole_0)), inference(resolution, [status(thm)], [c_224, c_233])).
% 7.08/2.77  tff(c_868, plain, (![A_89, B_90, C_91]: (k4_xboole_0(k3_xboole_0(A_89, B_90), C_91)=k3_xboole_0(A_89, k4_xboole_0(B_90, C_91)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.08/2.77  tff(c_69, plain, (![B_36, A_37]: (k3_xboole_0(B_36, A_37)=k3_xboole_0(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.08/2.77  tff(c_84, plain, (![B_36, A_37]: (r1_tarski(k3_xboole_0(B_36, A_37), A_37))), inference(superposition, [status(thm), theory('equality')], [c_69, c_22])).
% 7.08/2.77  tff(c_251, plain, (![B_36, A_37]: (k4_xboole_0(k3_xboole_0(B_36, A_37), A_37)=k1_xboole_0)), inference(resolution, [status(thm)], [c_84, c_233])).
% 7.08/2.77  tff(c_886, plain, (![A_89, C_91]: (k3_xboole_0(A_89, k4_xboole_0(C_91, C_91))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_868, c_251])).
% 7.08/2.77  tff(c_936, plain, (![A_89]: (k3_xboole_0(A_89, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_250, c_886])).
% 7.08/2.77  tff(c_332, plain, (![A_63, B_64]: (k3_xboole_0(A_63, B_64)=A_63 | ~r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.08/2.77  tff(c_354, plain, (![A_43]: (k3_xboole_0(A_43, A_43)=A_43)), inference(resolution, [status(thm)], [c_224, c_332])).
% 7.08/2.77  tff(c_3248, plain, (![B_137, A_138, C_139]: (k4_xboole_0(k3_xboole_0(B_137, A_138), C_139)=k3_xboole_0(A_138, k4_xboole_0(B_137, C_139)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_868])).
% 7.08/2.77  tff(c_7343, plain, (![A_183, C_184]: (k3_xboole_0(A_183, k4_xboole_0(A_183, C_184))=k4_xboole_0(A_183, C_184))), inference(superposition, [status(thm), theory('equality')], [c_354, c_3248])).
% 7.08/2.77  tff(c_252, plain, (![A_16, B_17]: (k4_xboole_0(k3_xboole_0(A_16, B_17), A_16)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_233])).
% 7.08/2.77  tff(c_7617, plain, (![A_187, C_188]: (k4_xboole_0(k4_xboole_0(A_187, C_188), A_187)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7343, c_252])).
% 7.08/2.77  tff(c_40, plain, (r1_tarski('#skF_2', k4_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.08/2.77  tff(c_357, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_3', '#skF_4'))='#skF_2'), inference(resolution, [status(thm)], [c_40, c_332])).
% 7.08/2.77  tff(c_907, plain, (![C_91]: (k3_xboole_0('#skF_2', k4_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), C_91))=k4_xboole_0('#skF_2', C_91))), inference(superposition, [status(thm), theory('equality')], [c_357, c_868])).
% 7.08/2.77  tff(c_7673, plain, (k4_xboole_0('#skF_2', '#skF_3')=k3_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7617, c_907])).
% 7.08/2.77  tff(c_7743, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_936, c_7673])).
% 7.08/2.77  tff(c_7745, plain, $false, inference(negUnitSimplification, [status(thm)], [c_318, c_7743])).
% 7.08/2.77  tff(c_7746, plain, (~r1_xboole_0('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_38])).
% 7.08/2.77  tff(c_8146, plain, (k3_xboole_0('#skF_2', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_8140, c_7746])).
% 7.08/2.77  tff(c_8149, plain, (k3_xboole_0('#skF_4', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8146])).
% 7.08/2.77  tff(c_7747, plain, (r1_tarski('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_38])).
% 7.08/2.77  tff(c_7911, plain, (![A_201, B_202]: (k3_xboole_0(A_201, B_202)=A_201 | ~r1_tarski(A_201, B_202))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.08/2.77  tff(c_7934, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_7747, c_7911])).
% 7.08/2.77  tff(c_9848, plain, (![A_265, B_266, C_267]: (k4_xboole_0(k3_xboole_0(A_265, B_266), C_267)=k3_xboole_0(A_265, k4_xboole_0(B_266, C_267)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.08/2.77  tff(c_12227, plain, (![C_300]: (k3_xboole_0('#skF_2', k4_xboole_0('#skF_3', C_300))=k4_xboole_0('#skF_2', C_300))), inference(superposition, [status(thm), theory('equality')], [c_7934, c_9848])).
% 7.08/2.77  tff(c_7936, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_3', '#skF_4'))='#skF_2'), inference(resolution, [status(thm)], [c_40, c_7911])).
% 7.08/2.77  tff(c_12276, plain, (k4_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_12227, c_7936])).
% 7.08/2.77  tff(c_7937, plain, (![A_203, B_204]: (k4_xboole_0(A_203, B_204)=k1_xboole_0 | ~r1_tarski(A_203, B_204))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.08/2.77  tff(c_7960, plain, (![A_16, B_17]: (k4_xboole_0(k3_xboole_0(A_16, B_17), A_16)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_7937])).
% 7.08/2.77  tff(c_9906, plain, (![A_16, B_17]: (k3_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7960, c_9848])).
% 7.08/2.77  tff(c_12347, plain, (k3_xboole_0('#skF_4', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_12276, c_9906])).
% 7.08/2.77  tff(c_12370, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8149, c_12347])).
% 7.08/2.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.08/2.77  
% 7.08/2.77  Inference rules
% 7.08/2.77  ----------------------
% 7.08/2.77  #Ref     : 0
% 7.08/2.77  #Sup     : 3118
% 7.08/2.77  #Fact    : 0
% 7.08/2.77  #Define  : 0
% 7.08/2.77  #Split   : 1
% 7.08/2.77  #Chain   : 0
% 7.08/2.77  #Close   : 0
% 7.08/2.77  
% 7.08/2.77  Ordering : KBO
% 7.08/2.78  
% 7.08/2.78  Simplification rules
% 7.08/2.78  ----------------------
% 7.08/2.78  #Subsume      : 72
% 7.08/2.78  #Demod        : 2798
% 7.08/2.78  #Tautology    : 2059
% 7.08/2.78  #SimpNegUnit  : 2
% 7.08/2.78  #BackRed      : 6
% 7.08/2.78  
% 7.08/2.78  #Partial instantiations: 0
% 7.08/2.78  #Strategies tried      : 1
% 7.08/2.78  
% 7.08/2.78  Timing (in seconds)
% 7.08/2.78  ----------------------
% 7.08/2.78  Preprocessing        : 0.32
% 7.08/2.78  Parsing              : 0.18
% 7.08/2.78  CNF conversion       : 0.02
% 7.08/2.78  Main loop            : 1.65
% 7.08/2.78  Inferencing          : 0.46
% 7.08/2.78  Reduction            : 0.82
% 7.08/2.78  Demodulation         : 0.70
% 7.08/2.78  BG Simplification    : 0.05
% 7.08/2.78  Subsumption          : 0.22
% 7.08/2.78  Abstraction          : 0.08
% 7.08/2.78  MUC search           : 0.00
% 7.08/2.78  Cooper               : 0.00
% 7.08/2.78  Total                : 2.01
% 7.08/2.78  Index Insertion      : 0.00
% 7.08/2.78  Index Deletion       : 0.00
% 7.08/2.78  Index Matching       : 0.00
% 7.08/2.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
