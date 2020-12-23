%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:22 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   52 (  67 expanded)
%              Number of leaves         :   19 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :   73 ( 102 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_xboole_1)).

tff(f_35,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(A,C)
        & r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,k4_xboole_0(B,C))
     => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(c_59,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(A_27,B_28)
      | k4_xboole_0(A_27,B_28) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_42,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_63,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_59,c_42])).

tff(c_14,plain,(
    ! [A_7,B_8] : r1_xboole_0(k4_xboole_0(A_7,B_8),B_8) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_16,plain,(
    ! [A_9,B_10,C_11] :
      ( r1_xboole_0(A_9,k4_xboole_0(B_10,C_11))
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_24,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_64,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = k1_xboole_0
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_72,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_64])).

tff(c_294,plain,(
    ! [A_51,B_52,C_53] :
      ( ~ r1_xboole_0(A_51,k4_xboole_0(B_52,C_53))
      | ~ r1_xboole_0(A_51,C_53)
      | r1_xboole_0(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_316,plain,(
    ! [A_51] :
      ( ~ r1_xboole_0(A_51,k1_xboole_0)
      | ~ r1_xboole_0(A_51,k4_xboole_0('#skF_2','#skF_3'))
      | r1_xboole_0(A_51,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_294])).

tff(c_401,plain,(
    ! [A_59] :
      ( ~ r1_xboole_0(A_59,k4_xboole_0('#skF_2','#skF_3'))
      | r1_xboole_0(A_59,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_316])).

tff(c_446,plain,(
    ! [A_60] :
      ( r1_xboole_0(A_60,'#skF_1')
      | ~ r1_xboole_0(A_60,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_401])).

tff(c_468,plain,(
    ! [A_61] : r1_xboole_0(k4_xboole_0(A_61,'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_446])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_480,plain,(
    ! [A_62] : r1_xboole_0('#skF_1',k4_xboole_0(A_62,'#skF_2')) ),
    inference(resolution,[status(thm)],[c_468,c_2])).

tff(c_18,plain,(
    ! [B_13,A_12,C_14] :
      ( r1_xboole_0(B_13,k4_xboole_0(A_12,C_14))
      | ~ r1_xboole_0(A_12,k4_xboole_0(B_13,C_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_500,plain,(
    ! [A_63] : r1_xboole_0(A_63,k4_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_480,c_18])).

tff(c_12,plain,(
    ! [A_6] :
      ( ~ r1_xboole_0(A_6,A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_514,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_500,c_12])).

tff(c_523,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_514])).

tff(c_524,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_35,plain,(
    ! [B_22,A_23] :
      ( r1_xboole_0(B_22,A_23)
      | ~ r1_xboole_0(A_23,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_40,plain,(
    ! [B_8,A_7] : r1_xboole_0(B_8,k4_xboole_0(A_7,B_8)) ),
    inference(resolution,[status(thm)],[c_14,c_35])).

tff(c_543,plain,(
    ! [A_69,B_70] :
      ( k4_xboole_0(A_69,B_70) = k1_xboole_0
      | ~ r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_555,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_543])).

tff(c_795,plain,(
    ! [A_89,B_90,C_91] :
      ( ~ r1_xboole_0(A_89,k4_xboole_0(B_90,C_91))
      | ~ r1_xboole_0(A_89,C_91)
      | r1_xboole_0(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_817,plain,(
    ! [A_89] :
      ( ~ r1_xboole_0(A_89,k1_xboole_0)
      | ~ r1_xboole_0(A_89,k4_xboole_0('#skF_2','#skF_3'))
      | r1_xboole_0(A_89,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_555,c_795])).

tff(c_887,plain,(
    ! [A_95] :
      ( ~ r1_xboole_0(A_95,k4_xboole_0('#skF_2','#skF_3'))
      | r1_xboole_0(A_95,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_817])).

tff(c_910,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_887])).

tff(c_915,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_910,c_2])).

tff(c_919,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_524,c_915])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.32  % Computer   : n018.cluster.edu
% 0.14/0.32  % Model      : x86_64 x86_64
% 0.14/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.32  % Memory     : 8042.1875MB
% 0.14/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.32  % CPULimit   : 60
% 0.14/0.32  % DateTime   : Tue Dec  1 13:46:26 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.38  
% 2.63/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.39  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.63/1.39  
% 2.63/1.39  %Foreground sorts:
% 2.63/1.39  
% 2.63/1.39  
% 2.63/1.39  %Background operators:
% 2.63/1.39  
% 2.63/1.39  
% 2.63/1.39  %Foreground operators:
% 2.63/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.63/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.63/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.63/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.63/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.63/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.63/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.63/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.39  
% 2.63/1.40  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.63/1.40  tff(f_72, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.63/1.40  tff(f_49, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.63/1.40  tff(f_53, axiom, (![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_xboole_1)).
% 2.63/1.40  tff(f_35, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.63/1.40  tff(f_65, axiom, (![A, B, C]: ~((~r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_xboole_1)).
% 2.63/1.40  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.63/1.40  tff(f_57, axiom, (![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_xboole_1)).
% 2.63/1.40  tff(f_47, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.63/1.40  tff(c_59, plain, (![A_27, B_28]: (r1_tarski(A_27, B_28) | k4_xboole_0(A_27, B_28)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.63/1.40  tff(c_22, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.63/1.40  tff(c_42, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_22])).
% 2.63/1.40  tff(c_63, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_59, c_42])).
% 2.63/1.40  tff(c_14, plain, (![A_7, B_8]: (r1_xboole_0(k4_xboole_0(A_7, B_8), B_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.63/1.40  tff(c_16, plain, (![A_9, B_10, C_11]: (r1_xboole_0(A_9, k4_xboole_0(B_10, C_11)) | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.63/1.40  tff(c_8, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.63/1.40  tff(c_24, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.63/1.40  tff(c_64, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=k1_xboole_0 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.63/1.40  tff(c_72, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_64])).
% 2.63/1.40  tff(c_294, plain, (![A_51, B_52, C_53]: (~r1_xboole_0(A_51, k4_xboole_0(B_52, C_53)) | ~r1_xboole_0(A_51, C_53) | r1_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.63/1.40  tff(c_316, plain, (![A_51]: (~r1_xboole_0(A_51, k1_xboole_0) | ~r1_xboole_0(A_51, k4_xboole_0('#skF_2', '#skF_3')) | r1_xboole_0(A_51, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_294])).
% 2.63/1.40  tff(c_401, plain, (![A_59]: (~r1_xboole_0(A_59, k4_xboole_0('#skF_2', '#skF_3')) | r1_xboole_0(A_59, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_316])).
% 2.63/1.40  tff(c_446, plain, (![A_60]: (r1_xboole_0(A_60, '#skF_1') | ~r1_xboole_0(A_60, '#skF_2'))), inference(resolution, [status(thm)], [c_16, c_401])).
% 2.63/1.40  tff(c_468, plain, (![A_61]: (r1_xboole_0(k4_xboole_0(A_61, '#skF_2'), '#skF_1'))), inference(resolution, [status(thm)], [c_14, c_446])).
% 2.63/1.40  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.63/1.40  tff(c_480, plain, (![A_62]: (r1_xboole_0('#skF_1', k4_xboole_0(A_62, '#skF_2')))), inference(resolution, [status(thm)], [c_468, c_2])).
% 2.63/1.40  tff(c_18, plain, (![B_13, A_12, C_14]: (r1_xboole_0(B_13, k4_xboole_0(A_12, C_14)) | ~r1_xboole_0(A_12, k4_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.63/1.40  tff(c_500, plain, (![A_63]: (r1_xboole_0(A_63, k4_xboole_0('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_480, c_18])).
% 2.63/1.40  tff(c_12, plain, (![A_6]: (~r1_xboole_0(A_6, A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.63/1.40  tff(c_514, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_500, c_12])).
% 2.63/1.40  tff(c_523, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_514])).
% 2.63/1.40  tff(c_524, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_22])).
% 2.63/1.40  tff(c_35, plain, (![B_22, A_23]: (r1_xboole_0(B_22, A_23) | ~r1_xboole_0(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.63/1.40  tff(c_40, plain, (![B_8, A_7]: (r1_xboole_0(B_8, k4_xboole_0(A_7, B_8)))), inference(resolution, [status(thm)], [c_14, c_35])).
% 2.63/1.40  tff(c_543, plain, (![A_69, B_70]: (k4_xboole_0(A_69, B_70)=k1_xboole_0 | ~r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.63/1.40  tff(c_555, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_543])).
% 2.63/1.40  tff(c_795, plain, (![A_89, B_90, C_91]: (~r1_xboole_0(A_89, k4_xboole_0(B_90, C_91)) | ~r1_xboole_0(A_89, C_91) | r1_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.63/1.40  tff(c_817, plain, (![A_89]: (~r1_xboole_0(A_89, k1_xboole_0) | ~r1_xboole_0(A_89, k4_xboole_0('#skF_2', '#skF_3')) | r1_xboole_0(A_89, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_555, c_795])).
% 2.63/1.40  tff(c_887, plain, (![A_95]: (~r1_xboole_0(A_95, k4_xboole_0('#skF_2', '#skF_3')) | r1_xboole_0(A_95, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_817])).
% 2.63/1.40  tff(c_910, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_40, c_887])).
% 2.63/1.40  tff(c_915, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_910, c_2])).
% 2.63/1.40  tff(c_919, plain, $false, inference(negUnitSimplification, [status(thm)], [c_524, c_915])).
% 2.63/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.40  
% 2.63/1.40  Inference rules
% 2.63/1.40  ----------------------
% 2.63/1.40  #Ref     : 0
% 2.63/1.40  #Sup     : 202
% 2.63/1.40  #Fact    : 0
% 2.63/1.40  #Define  : 0
% 2.63/1.40  #Split   : 2
% 2.63/1.40  #Chain   : 0
% 2.63/1.40  #Close   : 0
% 2.63/1.40  
% 2.63/1.40  Ordering : KBO
% 2.63/1.40  
% 2.63/1.40  Simplification rules
% 2.63/1.40  ----------------------
% 2.63/1.40  #Subsume      : 7
% 2.63/1.40  #Demod        : 131
% 2.63/1.40  #Tautology    : 125
% 2.63/1.40  #SimpNegUnit  : 2
% 2.63/1.40  #BackRed      : 4
% 2.63/1.40  
% 2.63/1.40  #Partial instantiations: 0
% 2.63/1.40  #Strategies tried      : 1
% 2.63/1.40  
% 2.63/1.40  Timing (in seconds)
% 2.63/1.40  ----------------------
% 2.63/1.40  Preprocessing        : 0.29
% 2.63/1.40  Parsing              : 0.17
% 2.63/1.40  CNF conversion       : 0.02
% 2.63/1.40  Main loop            : 0.33
% 2.63/1.40  Inferencing          : 0.12
% 2.63/1.40  Reduction            : 0.10
% 2.63/1.40  Demodulation         : 0.08
% 2.63/1.40  BG Simplification    : 0.02
% 2.63/1.40  Subsumption          : 0.06
% 2.63/1.40  Abstraction          : 0.01
% 2.63/1.40  MUC search           : 0.00
% 2.63/1.40  Cooper               : 0.00
% 2.63/1.40  Total                : 0.65
% 2.63/1.40  Index Insertion      : 0.00
% 2.63/1.40  Index Deletion       : 0.00
% 2.63/1.40  Index Matching       : 0.00
% 2.63/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
