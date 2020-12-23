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
% DateTime   : Thu Dec  3 09:57:23 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   50 (  74 expanded)
%              Number of leaves         :   28 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :   52 (  87 expanded)
%              Number of equality atoms :   37 (  58 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_52,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_54,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_75,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_48,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_73,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_36,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_87,plain,(
    ! [A_47,B_48] : k1_enumset1(A_47,A_47,B_48) = k2_tarski(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12,plain,(
    ! [E_11,A_5,C_7] : r2_hidden(E_11,k1_enumset1(A_5,E_11,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_105,plain,(
    ! [A_49,B_50] : r2_hidden(A_49,k2_tarski(A_49,B_50)) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_12])).

tff(c_108,plain,(
    ! [A_17] : r2_hidden(A_17,k1_tarski(A_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_105])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_128,plain,(
    ! [A_56,C_57,B_58] :
      ( ~ r2_hidden(A_56,C_57)
      | ~ r1_xboole_0(k2_tarski(A_56,B_58),C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_154,plain,(
    ! [A_60,C_61] :
      ( ~ r2_hidden(A_60,C_61)
      | ~ r1_xboole_0(k1_tarski(A_60),C_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_128])).

tff(c_198,plain,(
    ! [A_68,B_69] :
      ( ~ r2_hidden(A_68,B_69)
      | k3_xboole_0(k1_tarski(A_68),B_69) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_154])).

tff(c_202,plain,(
    ! [A_68] :
      ( ~ r2_hidden(A_68,k1_tarski(A_68))
      | k1_tarski(A_68) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_198])).

tff(c_204,plain,(
    ! [A_68] : k1_tarski(A_68) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_202])).

tff(c_48,plain,(
    ! [A_30] : k1_setfam_1(k1_tarski(A_30)) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_32,plain,(
    ! [A_12,B_13] : k2_xboole_0(k1_tarski(A_12),k1_tarski(B_13)) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_285,plain,(
    ! [A_85,B_86] :
      ( k3_xboole_0(k1_setfam_1(A_85),k1_setfam_1(B_86)) = k1_setfam_1(k2_xboole_0(A_85,B_86))
      | k1_xboole_0 = B_86
      | k1_xboole_0 = A_85 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_302,plain,(
    ! [A_30,B_86] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_30),B_86)) = k3_xboole_0(A_30,k1_setfam_1(B_86))
      | k1_xboole_0 = B_86
      | k1_tarski(A_30) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_285])).

tff(c_378,plain,(
    ! [A_98,B_99] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_98),B_99)) = k3_xboole_0(A_98,k1_setfam_1(B_99))
      | k1_xboole_0 = B_99 ) ),
    inference(negUnitSimplification,[status(thm)],[c_204,c_302])).

tff(c_404,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,k1_setfam_1(k1_tarski(B_13))) = k1_setfam_1(k2_tarski(A_12,B_13))
      | k1_tarski(B_13) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_378])).

tff(c_416,plain,(
    ! [A_12,B_13] :
      ( k1_setfam_1(k2_tarski(A_12,B_13)) = k3_xboole_0(A_12,B_13)
      | k1_tarski(B_13) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_404])).

tff(c_417,plain,(
    ! [A_12,B_13] : k1_setfam_1(k2_tarski(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(negUnitSimplification,[status(thm)],[c_204,c_416])).

tff(c_50,plain,(
    k1_setfam_1(k2_tarski('#skF_3','#skF_4')) != k3_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_422,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_417,c_50])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 12:02:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.36  
% 2.22/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.37  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.22/1.37  
% 2.22/1.37  %Foreground sorts:
% 2.22/1.37  
% 2.22/1.37  
% 2.22/1.37  %Background operators:
% 2.22/1.37  
% 2.22/1.37  
% 2.22/1.37  %Foreground operators:
% 2.22/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.22/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.22/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.22/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.22/1.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.22/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.22/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.22/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.22/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.37  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.22/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.22/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.22/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.22/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.22/1.37  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.22/1.37  
% 2.47/1.38  tff(f_52, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.47/1.38  tff(f_54, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.47/1.38  tff(f_46, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.47/1.38  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.47/1.38  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.47/1.38  tff(f_63, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.47/1.38  tff(f_75, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.47/1.38  tff(f_48, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.47/1.38  tff(f_73, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_setfam_1)).
% 2.47/1.38  tff(f_78, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.47/1.38  tff(c_36, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.47/1.38  tff(c_87, plain, (![A_47, B_48]: (k1_enumset1(A_47, A_47, B_48)=k2_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.47/1.38  tff(c_12, plain, (![E_11, A_5, C_7]: (r2_hidden(E_11, k1_enumset1(A_5, E_11, C_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.47/1.38  tff(c_105, plain, (![A_49, B_50]: (r2_hidden(A_49, k2_tarski(A_49, B_50)))), inference(superposition, [status(thm), theory('equality')], [c_87, c_12])).
% 2.47/1.38  tff(c_108, plain, (![A_17]: (r2_hidden(A_17, k1_tarski(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_105])).
% 2.47/1.38  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.47/1.38  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.47/1.38  tff(c_128, plain, (![A_56, C_57, B_58]: (~r2_hidden(A_56, C_57) | ~r1_xboole_0(k2_tarski(A_56, B_58), C_57))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.47/1.38  tff(c_154, plain, (![A_60, C_61]: (~r2_hidden(A_60, C_61) | ~r1_xboole_0(k1_tarski(A_60), C_61))), inference(superposition, [status(thm), theory('equality')], [c_36, c_128])).
% 2.47/1.38  tff(c_198, plain, (![A_68, B_69]: (~r2_hidden(A_68, B_69) | k3_xboole_0(k1_tarski(A_68), B_69)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_154])).
% 2.47/1.38  tff(c_202, plain, (![A_68]: (~r2_hidden(A_68, k1_tarski(A_68)) | k1_tarski(A_68)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_198])).
% 2.47/1.38  tff(c_204, plain, (![A_68]: (k1_tarski(A_68)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_108, c_202])).
% 2.47/1.38  tff(c_48, plain, (![A_30]: (k1_setfam_1(k1_tarski(A_30))=A_30)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.47/1.38  tff(c_32, plain, (![A_12, B_13]: (k2_xboole_0(k1_tarski(A_12), k1_tarski(B_13))=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.47/1.38  tff(c_285, plain, (![A_85, B_86]: (k3_xboole_0(k1_setfam_1(A_85), k1_setfam_1(B_86))=k1_setfam_1(k2_xboole_0(A_85, B_86)) | k1_xboole_0=B_86 | k1_xboole_0=A_85)), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.47/1.38  tff(c_302, plain, (![A_30, B_86]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_30), B_86))=k3_xboole_0(A_30, k1_setfam_1(B_86)) | k1_xboole_0=B_86 | k1_tarski(A_30)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_48, c_285])).
% 2.47/1.38  tff(c_378, plain, (![A_98, B_99]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_98), B_99))=k3_xboole_0(A_98, k1_setfam_1(B_99)) | k1_xboole_0=B_99)), inference(negUnitSimplification, [status(thm)], [c_204, c_302])).
% 2.47/1.38  tff(c_404, plain, (![A_12, B_13]: (k3_xboole_0(A_12, k1_setfam_1(k1_tarski(B_13)))=k1_setfam_1(k2_tarski(A_12, B_13)) | k1_tarski(B_13)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32, c_378])).
% 2.47/1.38  tff(c_416, plain, (![A_12, B_13]: (k1_setfam_1(k2_tarski(A_12, B_13))=k3_xboole_0(A_12, B_13) | k1_tarski(B_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_404])).
% 2.47/1.38  tff(c_417, plain, (![A_12, B_13]: (k1_setfam_1(k2_tarski(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(negUnitSimplification, [status(thm)], [c_204, c_416])).
% 2.47/1.38  tff(c_50, plain, (k1_setfam_1(k2_tarski('#skF_3', '#skF_4'))!=k3_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.47/1.38  tff(c_422, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_417, c_50])).
% 2.47/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.38  
% 2.47/1.38  Inference rules
% 2.47/1.38  ----------------------
% 2.47/1.38  #Ref     : 0
% 2.47/1.38  #Sup     : 82
% 2.47/1.38  #Fact    : 0
% 2.47/1.38  #Define  : 0
% 2.47/1.38  #Split   : 0
% 2.47/1.38  #Chain   : 0
% 2.47/1.38  #Close   : 0
% 2.47/1.38  
% 2.47/1.38  Ordering : KBO
% 2.47/1.38  
% 2.47/1.38  Simplification rules
% 2.47/1.38  ----------------------
% 2.47/1.38  #Subsume      : 4
% 2.47/1.38  #Demod        : 32
% 2.47/1.38  #Tautology    : 52
% 2.47/1.38  #SimpNegUnit  : 9
% 2.47/1.38  #BackRed      : 1
% 2.47/1.38  
% 2.47/1.38  #Partial instantiations: 0
% 2.47/1.38  #Strategies tried      : 1
% 2.47/1.38  
% 2.47/1.38  Timing (in seconds)
% 2.47/1.38  ----------------------
% 2.47/1.38  Preprocessing        : 0.30
% 2.47/1.38  Parsing              : 0.15
% 2.47/1.38  CNF conversion       : 0.02
% 2.47/1.38  Main loop            : 0.27
% 2.47/1.38  Inferencing          : 0.11
% 2.47/1.38  Reduction            : 0.08
% 2.47/1.38  Demodulation         : 0.06
% 2.47/1.38  BG Simplification    : 0.02
% 2.47/1.38  Subsumption          : 0.04
% 2.47/1.38  Abstraction          : 0.02
% 2.47/1.38  MUC search           : 0.00
% 2.47/1.38  Cooper               : 0.00
% 2.47/1.38  Total                : 0.60
% 2.47/1.38  Index Insertion      : 0.00
% 2.47/1.38  Index Deletion       : 0.00
% 2.47/1.39  Index Matching       : 0.00
% 2.47/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
