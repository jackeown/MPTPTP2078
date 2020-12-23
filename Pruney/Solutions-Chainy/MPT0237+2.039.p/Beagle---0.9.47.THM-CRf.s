%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:50 EST 2020

% Result     : Theorem 4.83s
% Output     : CNFRefutation 4.83s
% Verified   : 
% Statistics : Number of formulae       :   58 (  81 expanded)
%              Number of leaves         :   33 (  42 expanded)
%              Depth                    :    7
%              Number of atoms          :   51 (  84 expanded)
%              Number of equality atoms :   37 (  66 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( A != B
     => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_14,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [A_12,B_13] : r1_tarski(A_12,k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_105,plain,(
    ! [A_60,B_61] :
      ( k3_xboole_0(A_60,B_61) = A_60
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_128,plain,(
    ! [A_64,B_65] : k3_xboole_0(A_64,k2_xboole_0(A_64,B_65)) = A_64 ),
    inference(resolution,[status(thm)],[c_16,c_105])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_137,plain,(
    ! [A_64] : r1_tarski(A_64,A_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_10])).

tff(c_238,plain,(
    ! [A_79,B_80] :
      ( k4_xboole_0(A_79,B_80) = k1_xboole_0
      | ~ r1_tarski(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_259,plain,(
    ! [A_64] : k4_xboole_0(A_64,A_64) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_137,c_238])).

tff(c_418,plain,(
    ! [A_96,B_97] : k5_xboole_0(A_96,k4_xboole_0(B_97,A_96)) = k2_xboole_0(A_96,B_97) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_439,plain,(
    ! [A_64] : k5_xboole_0(A_64,k1_xboole_0) = k2_xboole_0(A_64,A_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_418])).

tff(c_446,plain,(
    ! [A_64] : k2_xboole_0(A_64,A_64) = A_64 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_439])).

tff(c_24,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_40,plain,(
    ! [A_48,B_49] :
      ( r1_xboole_0(k1_tarski(A_48),k1_tarski(B_49))
      | B_49 = A_48 ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_350,plain,(
    ! [A_89,B_90] :
      ( k4_xboole_0(A_89,B_90) = A_89
      | ~ r1_xboole_0(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1672,plain,(
    ! [A_157,B_158] :
      ( k4_xboole_0(k1_tarski(A_157),k1_tarski(B_158)) = k1_tarski(A_157)
      | B_158 = A_157 ) ),
    inference(resolution,[status(thm)],[c_40,c_350])).

tff(c_22,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2160,plain,(
    ! [B_168,A_169] :
      ( k5_xboole_0(k1_tarski(B_168),k1_tarski(A_169)) = k2_xboole_0(k1_tarski(B_168),k1_tarski(A_169))
      | B_168 = A_169 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1672,c_22])).

tff(c_42,plain,(
    ! [A_50,B_51] :
      ( k5_xboole_0(k1_tarski(A_50),k1_tarski(B_51)) = k2_tarski(A_50,B_51)
      | B_51 = A_50 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4195,plain,(
    ! [B_195,A_196] :
      ( k2_xboole_0(k1_tarski(B_195),k1_tarski(A_196)) = k2_tarski(B_195,A_196)
      | B_195 = A_196
      | B_195 = A_196 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2160,c_42])).

tff(c_38,plain,(
    ! [A_46,B_47] : k3_tarski(k2_tarski(A_46,B_47)) = k2_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_44,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_45,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_44])).

tff(c_4235,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_4195,c_45])).

tff(c_4239,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_1')) != k2_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4235,c_4235,c_45])).

tff(c_4242,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_446,c_24,c_4239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n007.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:26:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.83/1.95  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.83/1.95  
% 4.83/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.83/1.95  %$ r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 4.83/1.95  
% 4.83/1.95  %Foreground sorts:
% 4.83/1.95  
% 4.83/1.95  
% 4.83/1.95  %Background operators:
% 4.83/1.95  
% 4.83/1.95  
% 4.83/1.95  %Foreground operators:
% 4.83/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.83/1.95  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.83/1.95  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.83/1.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.83/1.95  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.83/1.95  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.83/1.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.83/1.95  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.83/1.95  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.83/1.95  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.83/1.95  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.83/1.95  tff('#skF_2', type, '#skF_2': $i).
% 4.83/1.95  tff('#skF_1', type, '#skF_1': $i).
% 4.83/1.95  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.83/1.95  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.83/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.83/1.95  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.83/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.83/1.95  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.83/1.95  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.83/1.95  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.83/1.95  
% 4.83/1.97  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.83/1.97  tff(f_43, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.83/1.97  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.83/1.97  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.83/1.97  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.83/1.97  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.83/1.97  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.83/1.97  tff(f_70, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 4.83/1.97  tff(f_47, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.83/1.97  tff(f_75, axiom, (![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 4.83/1.97  tff(f_65, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.83/1.97  tff(f_78, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 4.83/1.97  tff(c_14, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.83/1.97  tff(c_16, plain, (![A_12, B_13]: (r1_tarski(A_12, k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.83/1.97  tff(c_105, plain, (![A_60, B_61]: (k3_xboole_0(A_60, B_61)=A_60 | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.83/1.97  tff(c_128, plain, (![A_64, B_65]: (k3_xboole_0(A_64, k2_xboole_0(A_64, B_65))=A_64)), inference(resolution, [status(thm)], [c_16, c_105])).
% 4.83/1.97  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.83/1.97  tff(c_137, plain, (![A_64]: (r1_tarski(A_64, A_64))), inference(superposition, [status(thm), theory('equality')], [c_128, c_10])).
% 4.83/1.97  tff(c_238, plain, (![A_79, B_80]: (k4_xboole_0(A_79, B_80)=k1_xboole_0 | ~r1_tarski(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.83/1.97  tff(c_259, plain, (![A_64]: (k4_xboole_0(A_64, A_64)=k1_xboole_0)), inference(resolution, [status(thm)], [c_137, c_238])).
% 4.83/1.97  tff(c_418, plain, (![A_96, B_97]: (k5_xboole_0(A_96, k4_xboole_0(B_97, A_96))=k2_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.83/1.97  tff(c_439, plain, (![A_64]: (k5_xboole_0(A_64, k1_xboole_0)=k2_xboole_0(A_64, A_64))), inference(superposition, [status(thm), theory('equality')], [c_259, c_418])).
% 4.83/1.97  tff(c_446, plain, (![A_64]: (k2_xboole_0(A_64, A_64)=A_64)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_439])).
% 4.83/1.97  tff(c_24, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.83/1.97  tff(c_40, plain, (![A_48, B_49]: (r1_xboole_0(k1_tarski(A_48), k1_tarski(B_49)) | B_49=A_48)), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.83/1.97  tff(c_350, plain, (![A_89, B_90]: (k4_xboole_0(A_89, B_90)=A_89 | ~r1_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.83/1.97  tff(c_1672, plain, (![A_157, B_158]: (k4_xboole_0(k1_tarski(A_157), k1_tarski(B_158))=k1_tarski(A_157) | B_158=A_157)), inference(resolution, [status(thm)], [c_40, c_350])).
% 4.83/1.97  tff(c_22, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.83/1.97  tff(c_2160, plain, (![B_168, A_169]: (k5_xboole_0(k1_tarski(B_168), k1_tarski(A_169))=k2_xboole_0(k1_tarski(B_168), k1_tarski(A_169)) | B_168=A_169)), inference(superposition, [status(thm), theory('equality')], [c_1672, c_22])).
% 4.83/1.97  tff(c_42, plain, (![A_50, B_51]: (k5_xboole_0(k1_tarski(A_50), k1_tarski(B_51))=k2_tarski(A_50, B_51) | B_51=A_50)), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.83/1.97  tff(c_4195, plain, (![B_195, A_196]: (k2_xboole_0(k1_tarski(B_195), k1_tarski(A_196))=k2_tarski(B_195, A_196) | B_195=A_196 | B_195=A_196)), inference(superposition, [status(thm), theory('equality')], [c_2160, c_42])).
% 4.83/1.97  tff(c_38, plain, (![A_46, B_47]: (k3_tarski(k2_tarski(A_46, B_47))=k2_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.83/1.97  tff(c_44, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.83/1.97  tff(c_45, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_44])).
% 4.83/1.97  tff(c_4235, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_4195, c_45])).
% 4.83/1.97  tff(c_4239, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_1'))!=k2_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4235, c_4235, c_45])).
% 4.83/1.97  tff(c_4242, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_446, c_24, c_4239])).
% 4.83/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.83/1.97  
% 4.83/1.97  Inference rules
% 4.83/1.97  ----------------------
% 4.83/1.97  #Ref     : 0
% 4.83/1.97  #Sup     : 1021
% 4.83/1.97  #Fact    : 0
% 4.83/1.97  #Define  : 0
% 4.83/1.97  #Split   : 0
% 4.83/1.97  #Chain   : 0
% 4.83/1.97  #Close   : 0
% 4.83/1.97  
% 4.83/1.97  Ordering : KBO
% 4.83/1.97  
% 4.83/1.97  Simplification rules
% 4.83/1.97  ----------------------
% 4.83/1.97  #Subsume      : 120
% 4.83/1.97  #Demod        : 1552
% 4.83/1.97  #Tautology    : 817
% 4.83/1.97  #SimpNegUnit  : 0
% 4.83/1.97  #BackRed      : 5
% 4.83/1.97  
% 4.83/1.97  #Partial instantiations: 0
% 4.83/1.97  #Strategies tried      : 1
% 4.83/1.97  
% 4.83/1.97  Timing (in seconds)
% 4.83/1.97  ----------------------
% 4.83/1.97  Preprocessing        : 0.33
% 4.83/1.97  Parsing              : 0.18
% 4.83/1.97  CNF conversion       : 0.02
% 4.83/1.97  Main loop            : 0.87
% 4.83/1.97  Inferencing          : 0.25
% 4.83/1.97  Reduction            : 0.45
% 4.83/1.97  Demodulation         : 0.39
% 4.83/1.97  BG Simplification    : 0.03
% 4.83/1.97  Subsumption          : 0.10
% 4.83/1.97  Abstraction          : 0.05
% 4.83/1.97  MUC search           : 0.00
% 4.83/1.97  Cooper               : 0.00
% 4.83/1.97  Total                : 1.24
% 4.83/1.97  Index Insertion      : 0.00
% 4.83/1.97  Index Deletion       : 0.00
% 4.83/1.97  Index Matching       : 0.00
% 4.83/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
